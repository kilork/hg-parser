/*!
Crate `hg-parser` is Mercurial repository changelog parser. It allows to get any revision
with creation date, user, parents, branch and files.

# Installation

Add dependency to `Cargo.toml`:

```toml,ignore
[dependencies]
hg-parser = "0.6"
```

# Use case - Analyse revision log and export to ```git fast-import``` format

```rust
use hg_parser::{file_content, FileType, ManifestEntryDetails, MercurialRepository, Revision};

use std::env::args;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::string::ParseError;
use std::time::Instant;

fn export_repo<P: AsRef<Path>>(path: P) -> Result<(), Error> {
    let start = Instant::now();
    let repo = MercurialRepository::open(path)?;

    let stdout = std::io::stdout();
    let mut writer = stdout.lock();

    for changeset in &repo {
        let revision = changeset.revision;
        eprintln!("rev: {:?}", revision);

        let header = &changeset.header;
        let mut branch = None;
        let mut closed = false;
        for (key, value) in &header.extra {
            if key == b"branch" {
                branch = Some(value.as_slice());
            }

            if key == b"close" && value == b"1" {
                closed = true;
            }
        }

        let mut branch: Vec<_> = branch.unwrap_or_else(|| b"master").into();
        for b in branch.iter_mut() {
            if *b == b' ' {
                *b = b'-';
            }
        }

        let user = String::from_utf8_lossy(&header.user);
        let desc = String::from_utf8_lossy(&header.comment);

        let time = header.time.timestamp_secs();
        let timezone = header.time.tz_offset_secs();
        let tz = format!("{:+03}{:02}", -timezone / 3600, ((-timezone % 3600) / 60));

        write!(writer, "reset refs/heads/")?;
        writer.write_all(&mut branch)?;
        write!(writer, "\ncommit refs/heads/")?;
        writer.write_all(&mut branch)?;
        writeln!(writer, "\nmark :{}", mark(revision))?;

        writeln!(writer, "author {} {} {}", user, time, tz)?;
        writeln!(writer, "committer {} {} {}", user, time, tz)?;
        writeln!(writer, "data {}", desc.len() + 1)?;
        writeln!(writer, "{}\n", desc)?;

        match (header.p1, header.p2) {
            (Some(p1), Some(p2)) => {
                writeln!(writer, "from :{}", mark(p1))?;
                writeln!(writer, "merge :{}", mark(p2))?;
            }
            (Some(p), None) | (None, Some(p)) => {
                writeln!(writer, "from :{}", mark(p))?;
            }
            _ => (),
        }

        for mut file in changeset.files {
            match (file.data, file.manifest_entry) {
                (None, None) => {
                    write!(writer, "D ")?;
                    writer.write_all(&mut file.path)?;
                    writeln!(writer)?;
                }
                (Some(data), Some(manifest_entry)) => {
                    write!(
                        writer,
                        "M {} inline ",
                        match manifest_entry.details {
                            ManifestEntryDetails::File(FileType::Symlink) => "120000",
                            ManifestEntryDetails::File(FileType::Executable) => "100755",
                            ManifestEntryDetails::Tree
                            | ManifestEntryDetails::File(FileType::Regular) => "100644",
                        }
                    )?;
                    writer.write_all(&mut file.path)?;
                    let data = file_content(&data);
                    writeln!(writer, "\ndata {}", data.len())?;
                    writer.write_all(&data[..])?;
                }
                _ => panic!("Wrong file data!"),
            }
        }

        if closed {
            write!(writer, "reset refs/tags/archive/")?;
            writer.write_all(&mut branch)?;
            writeln!(writer, "\nfrom :{}\n", mark(revision))?;

            write!(writer, "reset refs/heads/")?;
            writer.write_all(&mut branch)?;
            writeln!(writer, "\nfrom 0000000000000000000000000000000000000000\n")?;
        }
    }

    for (rev, tag) in repo.tags().unwrap() {
        eprintln!("export tag {}", tag.name);
        writeln!(writer, "reset refs/tags/{}", tag.name).unwrap();
        writeln!(writer, "from :{}", mark(rev)).unwrap();
        writeln!(writer).unwrap();
    }

    eprintln!("Done. Elapsed: {:?}", start.elapsed());
    Ok(())
}

fn mark<R: Into<Revision>>(rev: R) -> usize {
    (rev.into() + 1).0 as usize
}

#[derive(Debug)]
enum Error {
    MercurialRepoException(hg_parser::ErrorKind),
    Parse(ParseError),
    IO(std::io::Error),
}

impl From<ParseError> for Error {
    fn from(value: ParseError) -> Self {
        Error::Parse(value)
    }
}

impl From<std::io::Error> for Error {
    fn from(value: std::io::Error) -> Self {
        Error::IO(value)
    }
}

impl From<hg_parser::ErrorKind> for Error {
    fn from(value: hg_parser::ErrorKind) -> Self {
        Error::MercurialRepoException(value)
    }
}
```

# Implementation details

`hg-parser` is based on repository parse code from [mononoke](https://github.com/facebookexperimental/mononoke) project. Which basically based on original Mercurial source code. Version has some simplifications which may not work for you.

*/
use lru_cache::LruCache;
use ordered_parallel_iterator::OrderedParallelIterator;
use rayon::prelude::*;
use std::collections::BTreeMap;
use std::collections::HashMap;
use std::collections::HashSet;
use std::fs::File;
use std::io::{BufRead, BufReader, Read};
use std::ops::Deref;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};

mod cache;
mod changeset;
mod error;
mod manifest;
mod parser;
mod path;
mod revisionlog;
mod types;

use cache::{Cachable, Cache};
pub use changeset::*;
pub use error::ErrorKind;
use manifest::Manifest;
use path::{fncache_fsencode, simple_fsencode, MPath, MPathElement};
use revisionlog::RevisionLog;
use types::{MercurialTag, NodeHash, RepositoryRequire};

pub use manifest::{FileType, ManifestEntry, ManifestEntryDetails};
pub use types::{Revision, RevisionRange};

#[derive(Debug)]
/// Mercurial repository. Top-level structure for access to change sets and tags.
pub struct MercurialRepository {
    root_path: PathBuf,
    changelog: RevisionLog,
    manifest: RevisionLog,
    requires: HashSet<RepositoryRequire>,
}

/// Cached version of `MercurialRepository`.
pub struct CachedMercurialRepository {
    repository: MercurialRepository,
    heads: Mutex<LruCache<Revision, Arc<Manifest>>>,
    files: Mutex<LruCache<Vec<u8>, Arc<RevisionLog>>>,
    cache: Cache,
}

impl From<MercurialRepository> for CachedMercurialRepository {
    fn from(repository: MercurialRepository) -> Self {
        Self {
            repository,
            heads: Mutex::new(LruCache::new(1 << 4)),
            files: Mutex::new(LruCache::new(1 << 12)),
            cache: Cache::new(1 << 13),
        }
    }
}

/// Shares instance of `CachedMercurialRepository` between multiple readers.
pub struct SharedMercurialRepository {
    inner: Arc<CachedMercurialRepository>,
}

impl SharedMercurialRepository {
    pub fn new(repository: MercurialRepository) -> Self {
        Self {
            inner: Arc::new(repository.into()),
        }
    }
}

impl Deref for SharedMercurialRepository {
    type Target = MercurialRepository;

    #[inline]
    fn deref(&self) -> &MercurialRepository {
        &self.inner.repository
    }
}

impl SharedMercurialRepository {
    pub fn par_range_iter(
        &self,
        revision_range: RevisionRange,
    ) -> OrderedParallelIterator<Changeset> {
        let cached_repository = self.inner.clone();
        let xform_ctor = move || {
            let cached_repository = cached_repository.clone();
            move |x: Revision| {
                let repository = &cached_repository.repository;
                repository
                    .changeset(
                        &cached_repository.heads,
                        &cached_repository.files,
                        &cached_repository.cache,
                        x,
                    )
                    .unwrap()
            }
        };
        OrderedParallelIterator::new(move || revision_range, xform_ctor)
    }
}

impl MercurialRepository {
    /// Opens `MercurialRepository` at `root_path`.
    pub fn open<P: AsRef<Path>>(root_path: P) -> Result<MercurialRepository, ErrorKind> {
        let base = root_path.as_ref().join(".hg");

        let requires = MercurialRepository::load_requires(&base)?;

        let store = base.join("store");

        let changelog = RevisionLog::init(store.join("00changelog.i"), None)?;
        let manifest = RevisionLog::init(store.join("00manifest.i"), None)?;

        Ok(MercurialRepository {
            root_path: root_path.as_ref().into(),
            changelog,
            manifest,
            requires,
        })
    }

    /// Last `Revision` in revision log.
    pub fn last_rev(&self) -> Revision {
        self.changelog.last_rev()
    }

    /// Changeset iterator other all revisions in log.
    pub fn iter(&self) -> ChangesetIter {
        self.into_iter()
    }

    /// Changeset header iterator other all revisions in log.
    pub fn header_iter(&self) -> ChangesetHeaderIter {
        self.range_header_iter(Revision::from(0).range_to(self.last_rev()))
    }

    /// Changeset iterator other range of revisions in log.
    pub fn range_iter<RR: Into<RevisionRange>>(&self, revisions_range: RR) -> ChangesetIter {
        ChangesetIter {
            repository: self,
            revisions_range: revisions_range.into(),
            heads: Mutex::new(LruCache::new(1 << 4)),
            files: Mutex::new(LruCache::new(1 << 12)),
            cache: Cache::new(1 << 13),
        }
    }

    /// Changeset header iterator other range of revisions in log.
    pub fn range_header_iter<RR: Into<RevisionRange>>(
        &self,
        revisions_range: RR,
    ) -> ChangesetHeaderIter {
        ChangesetHeaderIter {
            repository: self,
            revisions_range: revisions_range.into(),
            cache: Cache::new(1 << 13),
        }
    }

    /// List tags in repository. Tags read from `.hg/cache/tags2-visible` or `.hgtags`.
    pub fn tags(&self) -> Result<BTreeMap<Revision, MercurialTag>, ErrorKind> {
        let mut tags_path = self
            .root_path
            .join(".hg")
            .join("cache")
            .join("tags2-visible");
        if !tags_path.exists() {
            tags_path = self.root_path.join(".hgtags");
        }
        let file = File::open(tags_path)?;

        let mut names = HashMap::new();
        for line in BufReader::new(file).lines() {
            let tag: Result<MercurialTag, _> = line.unwrap().parse();
            if let Ok(tag) = tag {
                if let Some(rev) = self.changelog.info_revision_by_node(&tag.node).cloned() {
                    names.insert(tag.name.clone(), (rev, tag));
                } else {
                    names.remove(&tag.name);
                }
            }
        }
        Ok(names.into_iter().map(|(_, pair)| pair).collect())
    }

    pub(crate) fn get_manifest(&self, revision: Revision, cache: &Cache) -> Manifest {
        let data = self.changelog.get_revision(revision, cache).unwrap();
        let mut lines = data.splitn(2, |&x| x == b'\n');
        let manifestid: NodeHash = lines
            .next()
            .and_then(|x| std::str::from_utf8(x).ok())
            .and_then(|x| x.parse().ok())
            .unwrap();
        self.manifest
            .get_entry_by_nodeid(&manifestid)
            .and_then(|x| self.manifest.get_revision_from_entry(x, cache).ok())
            .map(Manifest::from)
            .unwrap()
    }

    fn load_requires<P: AsRef<Path>>(
        path: P,
    ) -> Result<HashSet<RepositoryRequire>, std::io::Error> {
        let requires_path = path.as_ref().join("requires");
        let file = File::open(requires_path)?;
        Ok(BufReader::new(file)
            .lines()
            .map(|x| x.unwrap().parse().expect("could not parse requirement"))
            .collect())
    }

    fn fsencode_path(&self, elements: &[MPathElement]) -> PathBuf {
        // Mercurial has a complicated logic of path encoding.
        // Code below matches core Mercurial logic from the commit
        // 75013952d8d9608f73cd45f68405fbd6ec112bf2 from file mercurial/store.py from the function
        // store(). The only caveat is that basicstore is not yet implemented
        if self.requires.contains(&RepositoryRequire::Store) {
            if self.requires.contains(&RepositoryRequire::FnCache) {
                let dotencode = self.requires.contains(&RepositoryRequire::DotEncode);
                fncache_fsencode(&elements, dotencode)
            } else {
                simple_fsencode(&elements)
            }
        } else {
            unimplemented!();
        }
    }

    fn changeset_header(&self, cache: &Cache, revision: Revision) -> Option<ChangesetHeader> {
        self.changelog.get_entry_by_revision(revision).map(|entry| {
            let data = self
                .changelog
                .get_revision_from_entry(entry, cache)
                .unwrap_or_else(|_| {
                    panic!(
                        "cannot get revision {:?} from changelog of {:?}",
                        revision, &self.root_path
                    )
                });
            ChangesetHeader::from_entry_bytes(entry, &data).unwrap()
        })
    }

    fn changeset(
        &self,
        heads: &Mutex<LruCache<Revision, Arc<Manifest>>>,
        files_cache: &Mutex<LruCache<Vec<u8>, Arc<RevisionLog>>>,
        cache: &Cache,
        revision: Revision,
    ) -> Option<Changeset> {
        if let Some(entry) = self.changelog.get_entry_by_revision(revision) {
            // we have entry - need to build revision and put it to heads

            let path = &self.root_path;
            let data = self
                .changelog
                .get_revision_from_entry(entry, cache)
                .unwrap_or_else(|_| {
                    panic!(
                        "cannot get revision {:?} from changelog of {:?}",
                        revision, path
                    )
                });
            let changeset_header = ChangesetHeader::from_entry_bytes(entry, &data).unwrap();
            if let Some(manifest_entry) = self
                .manifest
                .get_entry_by_nodeid(&changeset_header.manifestid)
                .or_else(|| self.manifest.get_entry_by_revision(revision))
            {
                let data = self
                    .manifest
                    .get_revision_from_entry(manifest_entry, cache)
                    .unwrap_or_else(|_| {
                        panic!(
                            "cannot get revision {:?} from manifest of {:?}",
                            revision, path
                        )
                    });
                let manifest = Manifest::from(data);

                let mut files = Vec::with_capacity(manifest.files.len() * 2);
                let files = if let (Some(p1), Some(p2)) = (changeset_header.p1, changeset_header.p2)
                {
                    let mut heads = heads.lock().unwrap();
                    if !heads.contains_key(&p1) {
                        heads.insert(p1, Arc::new(self.get_manifest(p1, cache)));
                    }
                    if !heads.contains_key(&p2) {
                        heads.insert(p2, Arc::new(self.get_manifest(p2, cache)));
                    }

                    let p1 = heads.get_mut(&p1).cloned().unwrap();
                    let p2 = heads.get_mut(&p2).cloned().unwrap();

                    split_dict(&manifest, &p1, &mut files);
                    split_dict(&manifest, &p2, &mut files);

                    files.sort();
                    files.dedup();

                    &files
                } else {
                    &changeset_header.files
                };

                let files: Vec<_> = files
                    .par_iter()
                    .map(|file| {
                        let file = file.as_slice();
                        let manifest_entry = manifest.files.get(file);
                        let data = manifest_entry.and_then(|manifest_entry| {
                            Self::file_revlog(self, files_cache, file)
                                .get_revision_by_nodeid(&manifest_entry.id, cache)
                        });

                        ChangesetFile {
                            path: file.into(),
                            data,
                            manifest_entry: manifest_entry.cloned(),
                        }
                    })
                    .collect();
                heads
                    .lock()
                    .as_mut()
                    .map(|x| {
                        changeset_header.p1.map(|h1| x.remove(&h1));
                        changeset_header.p2.map(|h2| x.remove(&h2));
                        x.insert(revision, Arc::new(manifest));
                    })
                    .unwrap();
                let changeset = Changeset {
                    revision,
                    header: changeset_header,
                    files,
                };
                Some(changeset)
            } else {
                None
            }
        } else {
            // revision does not exist - stop iterator
            None
        }
    }

    fn file_revlog(
        repository: &MercurialRepository,
        files: &Mutex<LruCache<Vec<u8>, Arc<RevisionLog>>>,
        file: &[u8],
    ) -> Arc<RevisionLog> {
        let mut file_revlog = files.lock().unwrap().get_mut(file).cloned();

        if file_revlog.is_none() {
            let filerevlog = Arc::new(Self::init_file_revlog(repository, file));
            files
                .lock()
                .unwrap()
                .insert(file.into(), filerevlog.clone());
            assert!(files.lock().unwrap().get_mut(file).is_some());
            file_revlog = Some(filerevlog);
        }

        file_revlog.unwrap()
    }

    fn init_file_revlog(repository: &MercurialRepository, file: &[u8]) -> RevisionLog {
        let root_path = &repository.root_path;
        let path = MPath::from(file);
        let path = MPath::new("data")
            .unwrap()
            .join(MPath::iter_opt(Some(&path)));

        let mut elements: Vec<MPathElement> = path.into_iter().collect();
        let mut basename = elements.pop().unwrap();

        let index_path = {
            let mut basename = basename.clone();
            basename.extend(b".i");
            elements.push(basename);
            repository.fsencode_path(&elements)
        };
        elements.pop();

        let data_path = {
            basename.extend(b".d");
            elements.push(basename);
            repository.fsencode_path(&elements)
        };

        let store = root_path.join(".hg").join("store");
        match RevisionLog::init(store.join(index_path), Some(store.join(data_path))) {
            Err(ErrorKind::InvalidPath(info)) => Err(ErrorKind::InvalidPath(format!(
                "Cannot load revision log for {:?}: {}",
                std::str::from_utf8(&file),
                info
            ))),
            other => other,
        }
        .unwrap()
    }
}

impl<'a> IntoIterator for &'a MercurialRepository {
    type Item = Changeset;
    type IntoIter = ChangesetIter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.range_iter(Revision::from(0).range_to(self.last_rev()))
    }
}

/// Iterator over `MercurialRepository` revisions.
pub struct ChangesetIter<'a> {
    repository: &'a MercurialRepository,
    revisions_range: RevisionRange,
    heads: Mutex<LruCache<Revision, Arc<Manifest>>>,
    files: Mutex<LruCache<Vec<u8>, Arc<RevisionLog>>>,
    cache: Cache,
}

impl<'a> Iterator for ChangesetIter<'a> {
    type Item = Changeset;

    fn next(&mut self) -> Option<Self::Item> {
        self.revisions_range.next().and_then(|revision| {
            self.repository
                .changeset(&self.heads, &self.files, &self.cache, revision)
        })
    }
}

pub struct ChangesetHeaderIter<'a> {
    repository: &'a MercurialRepository,
    revisions_range: RevisionRange,
    cache: Cache,
}

impl<'a> Iterator for ChangesetHeaderIter<'a> {
    type Item = ChangesetHeader;

    fn next(&mut self) -> Option<Self::Item> {
        self.revisions_range
            .next()
            .and_then(|revision| self.repository.changeset_header(&self.cache, revision))
    }
}

fn load_to_vec<P: AsRef<Path>>(path: P) -> Result<Vec<u8>, ErrorKind> {
    let mut f = match File::open(path.as_ref()) {
        Ok(f) => f,
        Err(err) => {
            return Err(ErrorKind::InvalidPath(format!(
                "Cannot open {:?}: {:?}",
                path.as_ref(),
                err
            )));
        }
    };
    let mut result = vec![];
    f.read_to_end(&mut result).unwrap();
    Ok(result)
}

/// Extract blob data (raw file content) from internal Mercurial representation.
/// This representation is by default returned by [ChangesetIter](struct.ChangesetIter.html) iterator.
/// ```
/// # use hg_parser::file_content;
/// let blob_with_meta = b"\x01\nmeta information\x01\nraw body";
///
/// let blob = file_content(blob_with_meta);
///
/// assert_eq!(blob, b"raw body");
///
/// assert_eq!(b"without meta", file_content(b"without meta"));
/// ```
pub fn file_content(data: &[u8]) -> &[u8] {
    let (_, off) = extract_meta(data);
    &data[off..]
}

const META_MARKER: &[u8] = b"\x01\n";
const META_SZ: usize = 2;

fn extract_meta(file: &[u8]) -> (&[u8], usize) {
    if file.len() < META_SZ {
        return (&[], 0);
    }
    if &file[..META_SZ] != META_MARKER {
        (&[], 0)
    } else {
        let metasz = &file[META_SZ..]
            .windows(2)
            .enumerate()
            .find(|&(_, sample)| sample == META_MARKER)
            .map(|(idx, _)| idx + META_SZ * 2)
            .unwrap_or(META_SZ); // XXX malformed if None - unterminated metadata

        let metasz = *metasz;
        if metasz >= META_SZ * 2 {
            (&file[META_SZ..metasz - META_SZ], metasz)
        } else {
            (&[], metasz)
        }
    }
}

fn split_dict(dleft: &Manifest, dright: &Manifest, f: &mut Vec<Vec<u8>>) {
    for (left, linfo) in &dleft.files {
        let right = dright.files.get(left);
        if right.is_none() || right.unwrap() != linfo {
            f.push(left.clone());
        }
    }

    for right in dright.files.keys() {
        let left = dleft.files.get(right);
        if left.is_none() {
            f.push(right.clone());
        }
    }
}

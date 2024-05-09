use std::{
    cmp,
    collections::{BTreeMap, HashMap},
    path::{Path, PathBuf},
    sync::Arc,
};

use super::{
    cache::{Cachable, Cache},
    load_to_vec, parser,
    types::{
        Chunk, Delta, Features, Fragment, NodeHash, Revision, RevisionLogEntry, RevisionLogHeader,
        Version,
    },
    ErrorKind,
};

/// Mercurial revision log information.
#[derive(Debug)]
pub(crate) struct RevisionLog {
    header: RevisionLogHeader,
    index: Vec<u8>,
    data: Option<Vec<u8>>,
    info: Info,
    is_general_delta: bool,
    is_inline: bool,
}

#[derive(Debug)]
struct Info {
    offsets: BTreeMap<Revision, usize>,
    nodes: HashMap<NodeHash, Revision>,
    entries: HashMap<Revision, RevisionLogEntry>,
}

impl RevisionLog {
    pub(crate) fn init<P: AsRef<Path>>(path: P, data_path: Option<P>) -> Result<Self, ErrorKind> {
        let index = load_to_vec(path.as_ref())?;

        let (_, header) = parser::header(&index)?;

        let data = if !header.features.contains(Features::INLINE) {
            let datapath: PathBuf = data_path
                .map(|x| x.as_ref().into())
                .unwrap_or_else(|| path.as_ref().with_extension("d"));
            Some(load_to_vec(datapath)?)
        } else {
            None
        };

        let mut revision_log = RevisionLog {
            header,
            index,
            data,
            info: Info {
                offsets: BTreeMap::new(),
                nodes: HashMap::new(),
                entries: HashMap::new(),
            },
            is_general_delta: header.features.contains(Features::GENERAL_DELTA),
            is_inline: header.features.contains(Features::INLINE),
        };

        let mut offset = 0;
        let mut i = 0.into();

        loop {
            let entry = revision_log.parse_entry(offset);
            if let Ok(entry) = entry {
                revision_log.info.offsets.insert(i, offset);
                revision_log.info.nodes.insert(entry.nodeid, i);
                revision_log.info.entries.insert(i, entry);
                offset += revision_log.entry_size(Some(&entry));
                i = i + 1;
            } else {
                break;
            }
        }

        Ok(revision_log)
    }

    #[inline]
    pub(crate) fn get_entry_by_revision(&self, revision: Revision) -> Option<&RevisionLogEntry> {
        self.info.entries.get(&revision)
    }

    #[inline]
    pub(crate) fn get_entry_by_nodeid(&self, nodeid: &NodeHash) -> Option<&RevisionLogEntry> {
        self.info
            .nodes
            .get(nodeid)
            .and_then(|revision| self.info.entries.get(revision))
    }

    pub(crate) fn get_revision_by_nodeid(
        &self,
        nodeid: &NodeHash,
        cache: &Cache,
    ) -> Option<Arc<[u8]>> {
        self.info
            .nodes
            .get(nodeid)
            .and_then(|&revision| self.get_revision(revision, cache).ok())
    }

    pub(crate) fn get_revision_from_entry(
        &self,
        entry: &RevisionLogEntry,
        cache: &Cache,
    ) -> Result<Arc<[u8]>, ErrorKind> {
        let tgtrev = *self.info.nodes.get(&entry.nodeid).unwrap();
        self.get_revision(tgtrev, cache)
    }

    #[inline]
    pub(crate) fn get_revision(
        &self,
        revision: Revision,
        cache: &Cache,
    ) -> Result<Arc<[u8]>, ErrorKind> {
        if self.is_general_delta() {
            self.construct_general(revision, cache)
        } else {
            self.construct_simple(revision)
        }
    }

    pub fn info_revision_by_node(&self, node: &NodeHash) -> Option<&Revision> {
        self.info.nodes.get(node)
    }

    /// Return a `Chunk` for a revision at `RevIdx`.
    ///
    /// A `Chunk` either represents the literal
    /// text of the change, or a series of deltas against a previous version; the exact
    /// mechanism of applying the deltas depends on whether the `RevLog` has the `GENERAL_DELTA`
    /// flag set or not.
    fn get_chunk(&self, idx: Revision) -> Result<Chunk, ErrorKind> {
        let entry = self.get_entry_by_revision(idx).unwrap();

        let (chunkdata, start): (&[u8], usize) = if self.is_inline {
            let off = self.offset_for_idx(idx).expect("not cached?");
            let start = off + self.fixed_entry_size();

            (&self.index, start)
        } else {
            let start = entry.offset as usize;

            (self.data.as_ref().expect("non-inline has no data"), start)
        };
        let end = start + (entry.compressed_len as usize);
        let chunkdata = &chunkdata[start..end];

        // If the entry has baserev that is equal to it's idx, then the chunk is literal data.
        // Otherwise its 0 or more deltas against the baserev. If its general delta, then the
        // baserev itself might also be delta, otherwise its all the deltas from baserev..idx.
        if Some(idx) == entry.baserev {
            if chunkdata.is_empty() {
                Ok(Chunk::Literal(vec![].into()))
            } else {
                match parser::literal(chunkdata) {
                    Ok((rest, _)) if !rest.is_empty() => {
                        Err(ErrorKind::RevisionLogFailure(format!(
                            "Failed to unpack literal: {} remains, {:?}",
                            rest.len(),
                            &rest[..16]
                        )))
                    }
                    Ok((_, literal)) => Ok(Chunk::Literal(literal)),
                    err => Err(ErrorKind::RevisionLogFailure(format!(
                        "Failed to unpack literal: {:?}",
                        err
                    ))),
                }
            }
        } else {
            match parser::deltachunk(chunkdata) {
                Ok((rest, _)) if !rest.is_empty() => Err(ErrorKind::RevisionLogFailure(format!(
                    "Failed to unpack details: {} remains, {:?}",
                    rest.len(),
                    &rest[..16]
                ))),
                Ok((_, deltas)) => Ok(Chunk::Deltas(deltas)),
                err => Err(ErrorKind::RevisionLogFailure(format!(
                    "Failed to unpack deltas: {:?}",
                    err
                ))),
            }
        }
    }

    fn offset_for_idx(&self, idx: Revision) -> Option<usize> {
        if self.is_inline {
            self.info.offsets.get(&idx).cloned()
        } else {
            Some(idx.0 as usize * self.entry_size(None))
        }
    }

    fn construct_simple(&self, tgtidx: Revision) -> Result<Arc<[u8]>, ErrorKind> {
        assert!(!self.is_general_delta());

        let entry = self.get_entry_by_revision(tgtidx).unwrap();
        // if there's no baserev, then use the target as a baserev (it should be literal)
        let baserev = entry.baserev.map(Into::into).unwrap_or(tgtidx);

        // non-general delta - baserev should be literal, then we applying
        // each delta up to idx
        let mut data = None;
        let mut chain = Vec::new();
        for idx in baserev.range_to(tgtidx + 1).rev() {
            let chunk = self.get_chunk(idx);

            match chunk? {
                Chunk::Literal(v) => {
                    data = Some(v);
                    break;
                }
                Chunk::Deltas(deltas) => {
                    chain.push(deltas);
                }
            }
        }

        if chain.is_empty() {
            return Ok(data.clone().unwrap_or_else(|| Arc::from(Vec::new())));
        }

        let data = apply_chain(data.as_deref().unwrap_or_default(), chain.into_iter().rev())?;
        Ok(data.into())
    }

    fn construct_general(&self, tgtidx: Revision, cache: &Cache) -> Result<Arc<[u8]>, ErrorKind> {
        assert!(self.is_general_delta());

        let mut chunks = Vec::new();
        let mut idx = tgtidx;

        // general delta - walk backwards until we hit a literal, collecting chunks on the way
        let data = loop {
            chunks.push(idx);

            let chunk = self.get_chunk(idx)?;

            // We have three valid cases:
            // 1) Literal chunk - this is possible only if baserev == idx
            // 2) Delta against empty string - this is possible only if baserev is None.
            //    In core hg it matches a case where baserev == -1.
            // 3) Delta against non-empty string. Only if baserev is Some(...) and baserev < idx.
            let entry = self.get_entry_by_revision(idx).unwrap();
            match entry.baserev {
                Some(baseidx) if idx == baseidx => {
                    // This is a literal
                    match chunk {
                        Chunk::Literal(v) => {
                            chunks.pop();
                            break v;
                        }
                        _ => {
                            return Err(ErrorKind::RevisionLogFailure(
                                "expected a literal".to_string(),
                            ));
                        }
                    }
                }
                Some(baseidx) if idx > baseidx => {
                    idx = baseidx;
                    let base_entry = self.get_entry_by_revision(baseidx).unwrap();
                    if let Some(data) = cache.get(&base_entry.nodeid) {
                        break data;
                    }
                }
                Some(baseidx) => {
                    return Err(ErrorKind::RevisionLogFailure(format!(
                        "baserev {:?} >= idx {:?}",
                        baseidx, idx
                    )));
                }
                None => match chunk {
                    // This is a delta against "-1" revision i.e. empty revision
                    Chunk::Deltas(_) => {
                        break vec![].into();
                    }
                    _ => {
                        return Err(ErrorKind::RevisionLogFailure(
                            "expected a delta against empty string".to_string(),
                        ));
                    }
                },
            }
        };

        if chunks.is_empty() {
            return Ok(cache.put(self.get_entry_by_revision(tgtidx).unwrap().nodeid, data));
        }

        let chain = chunks.into_iter().rev().map(|idx| {
            let chunk = self.get_chunk(idx);

            match chunk {
                Ok(Chunk::Deltas(deltas)) => deltas,
                _ => panic!("Literal text found in delta chain."),
            }
        });

        let data = apply_chain(data.as_ref(), chain)?;
        Ok(cache.put(
            self.get_entry_by_revision(tgtidx).unwrap().nodeid,
            data.into(),
        ))
    }

    #[inline]
    fn is_general_delta(&self) -> bool {
        self.is_general_delta
    }

    fn fixed_entry_size(&self) -> usize {
        match self.header.version {
            Version::Revlog0 => parser::index0_size(),
            Version::RevlogNG => parser::indexng_size(),
        }
    }

    fn entry_size(&self, entry: Option<&RevisionLogEntry>) -> usize {
        let mut size = self.fixed_entry_size();
        if self.header.features.contains(Features::INLINE) {
            size += entry.expect("inline needs ent").compressed_len as usize;
        }
        size
    }

    pub fn last_rev(&self) -> Revision {
        (self.info.entries.len() as u32).into()
    }

    fn parse_entry(&mut self, offset: usize) -> Result<RevisionLogEntry, ErrorKind> {
        let data = &self.index[offset..];

        let entry = match self.header.version {
            Version::Revlog0 => parser::index0(data),
            Version::RevlogNG => parser::indexng(data),
        };

        match entry {
            Ok((_, mut entry)) => {
                if offset == 0 {
                    entry.offset &= 0xffff;
                }
                Ok(entry)
            }
            err => Err(ErrorKind::RevisionLogFailure(format!(
                "cannot parse changelog at {}: {:?}",
                offset, err
            ))),
        }
    }
}

/// Apply a chain of Deltas to an input text, returning the result.
/// Pack all deltas into one delta, and apply a pack to input text.
pub fn apply_chain<I: IntoIterator<Item = Delta>>(
    text: &[u8],
    deltas: I,
) -> Result<Vec<u8>, ErrorKind> {
    let mut res = Vec::from(text);

    let (wrapped_deltas, data) = wrap_deltas(deltas);

    if wrapped_deltas.is_empty() {
        Ok(res)
    } else {
        // fold all deltas into one delta using logarithmic algorithm
        let folded_wrapped_delta = mpatch_fold(&wrapped_deltas, 0, wrapped_deltas.len());

        // convert into Revlog Delta
        let folded_delta = folded_wrapped_delta.delta(&data)?;

        // apply folded delta
        res = apply(&res, &folded_delta)?;
        Ok(res)
    }
}

/// Apply a Delta to an input text, returning the result.
pub fn apply(text: &[u8], delta: &Delta) -> Result<Vec<u8>, ErrorKind> {
    let mut chunks = Vec::with_capacity(delta.fragments.len() * 2);
    let mut off = 0;

    for frag in &delta.fragments {
        assert!(
            off <= frag.start,
            "Invalid delta, fragment start is less than current offset ({} < {})",
            frag.start,
            off
        );
        if off < frag.start {
            chunks.push(text.get(off..frag.start).ok_or_else(|| {
                ErrorKind::RevisionLogFailure(format!(
                    "Invalid delta, the range {}..{} is out of bounds for provided text",
                    off, frag.start
                ))
            })?);
        }
        if !frag.content.is_empty() {
            chunks.push(frag.content.as_ref())
        }
        off = frag.end;
    }

    match off.cmp(&text.len()) {
        cmp::Ordering::Less => chunks.push(&text[off..text.len()]),
        cmp::Ordering::Equal => (),
        cmp::Ordering::Greater => {
            return Err(ErrorKind::RevisionLogFailure(format!(
                "Invalid delta, fragment is referencing out of bounds content: {} > {}",
                off,
                text.len()
            )))
        }
    }

    let size = chunks.iter().map(|c| c.len()).sum::<usize>();
    let mut output = Vec::with_capacity(size);
    for c in chunks {
        output.extend_from_slice(c);
    }
    Ok(output)
}

/*
* Algorithm is taken from fbcode/scm/hg/mercurial/mpatch.c
*/

/// Wrap all Fragments and return FragmentWrapperIterator.
/// Gather all contents hold fragments contents in one vector.
pub fn wrap_deltas<I: IntoIterator<Item = Delta>>(
    deltas: I,
) -> (Vec<FragmentWrapperIterator>, Vec<u8>) {
    let mut wrapped_deltas = Vec::new();
    let mut data = Vec::new();
    let mut content_offset = 0;

    for delta in deltas {
        let wrapped_delta = FragmentWrapperIterator::new(&delta, content_offset as i64);
        for frag in delta.fragments() {
            data.extend_from_slice(frag.content.as_ref());
            content_offset += frag.content.len();
        }

        wrapped_deltas.push(wrapped_delta);
    }

    (wrapped_deltas, data)
}

// Fragment Wrapper, it does not have actual data, only references to real data
#[derive(Clone, Eq, Debug, PartialEq, Ord, PartialOrd)]
pub struct FragmentWrapper {
    pub start: i64,
    pub end: i64,
    pub len: i64,
    pub content_start: i64,
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Default)]
pub struct FragmentWrapperIterator {
    // Struct for holding Fragments and updating current head
    frags: Vec<FragmentWrapper>,
    cur_pointer: usize,
}

impl FragmentWrapperIterator {
    pub(crate) fn new(delta: &Delta, content_offset: i64) -> FragmentWrapperIterator {
        // Convert Delta to Vec<FragmentWrapper>, using global offset of the content in Content Bytes
        let mut frag_wrappers = Vec::new();
        let mut offset = content_offset;

        for frag in delta.fragments() {
            let frag_wrapper = FragmentWrapper {
                start: frag.start as i64,
                end: frag.end as i64,
                len: frag.content_length() as i64,
                content_start: offset,
            };
            offset += frag.content_length() as i64;
            frag_wrappers.push(frag_wrapper);
        }

        FragmentWrapperIterator {
            frags: frag_wrappers,
            cur_pointer: 0,
        }
    }

    pub(crate) fn current_fragment_mut(&mut self) -> &mut FragmentWrapper {
        &mut self.frags[self.cur_pointer]
    }

    pub(crate) fn current_fragment(&self) -> &FragmentWrapper {
        &self.frags[self.cur_pointer]
    }

    pub(crate) fn end(&self) -> bool {
        self.cur_pointer == self.frags.len()
    }

    pub(crate) fn go_next(&mut self) {
        self.cur_pointer += 1;
    }

    pub(crate) fn set_start(&mut self) {
        self.cur_pointer = 0;
    }

    pub(crate) fn fragments(&self) -> &[FragmentWrapper] {
        self.frags.as_slice()
    }

    pub(crate) fn push(&mut self, frag: FragmentWrapper) {
        self.frags.push(frag);
    }

    pub(crate) fn delta(&self, data: &[u8]) -> Result<Delta, ErrorKind> {
        let mut frags = Vec::new();

        for frag_wrapper in self.frags.as_slice() {
            let content_start = frag_wrapper.content_start as usize;
            let content_len = frag_wrapper.len as usize;
            let content_end = content_start + content_len;

            let frag = Fragment {
                start: frag_wrapper.start as usize,
                end: frag_wrapper.end as usize,
                content: data[content_start..content_end].into(),
            };
            frags.push(frag);
        }
        Delta::new(frags)
    }
}

/// Fold deltas in the range [start, end)
pub(crate) fn mpatch_fold(
    deltas: &[FragmentWrapperIterator],
    start: usize,
    end: usize,
) -> FragmentWrapperIterator {
    assert!(start < end);

    if start + 1 == end {
        deltas[start].clone()
    } else {
        let half_deltas_cnt = (end - start) / 2;
        combine(
            &mut mpatch_fold(deltas, start, start + half_deltas_cnt),
            &mut mpatch_fold(deltas, start + half_deltas_cnt, end),
        )
    }
}

/// Merge 2 sequential deltas into 1 delta
fn combine(
    a: &mut FragmentWrapperIterator,
    b: &mut FragmentWrapperIterator,
) -> FragmentWrapperIterator {
    let mut combined: FragmentWrapperIterator = Default::default();
    let mut offset = 0;
    let mut post;

    a.set_start();
    for b_frag in b.fragments() {
        offset = gather(&mut combined, a, b_frag.start, offset);

        post = discard(a, b_frag.end, offset);

        let frag = FragmentWrapper {
            start: b_frag.start - offset,
            end: b_frag.end - post,
            len: b_frag.len,
            content_start: b_frag.content_start,
        };
        combined.push(frag);
        offset = post;
    }

    // process tail
    while !a.end() {
        combined.push(a.current_fragment().clone());
        a.go_next();
    }
    combined
}

/// Copy all fragments from src to dst until cut
fn gather(
    dst: &mut FragmentWrapperIterator,
    src: &mut FragmentWrapperIterator,
    cut: i64,
    mut offset: i64,
) -> i64 {
    while !src.end() {
        let frag = src.current_fragment().clone();

        if frag.start + offset >= cut {
            break;
        }

        let postend = offset + frag.start + frag.len;
        if postend <= cut {
            offset += frag.start + frag.len - frag.end;
            dst.push(frag.clone());

            src.go_next();
        } else {
            let new_start = cmp::min(cut - offset, frag.end);
            let prev_len = cmp::min(cut - offset - frag.start, frag.len);

            offset += frag.start + prev_len - new_start;

            let prev_content_start = frag.content_start;
            let new_content_start = frag.content_start + prev_len;

            let new_frag = FragmentWrapper {
                start: frag.start,
                end: new_start,
                len: prev_len,
                content_start: prev_content_start,
            };

            dst.push(new_frag);

            let frag_mut = src.current_fragment_mut();

            frag_mut.start = new_start;
            frag_mut.len = frag.len - prev_len;
            frag_mut.content_start = new_content_start;
            break;
        }
    }
    offset
}

/// Delete all fragments from src until cut
fn discard(src: &mut FragmentWrapperIterator, cut: i64, mut offset: i64) -> i64 {
    while !src.end() {
        let frag = src.current_fragment().clone();

        if frag.start + offset >= cut {
            break;
        }

        let postend = offset + frag.start + frag.len;
        if postend <= cut {
            offset += frag.start + frag.len - frag.end;
            src.go_next();
        } else {
            let new_start = cmp::min(cut - offset, frag.end);
            let prev_len = cmp::min(cut - offset - frag.start, frag.len);

            offset += frag.start + prev_len - new_start;

            let new_content_start = frag.content_start + prev_len;

            let frag_mut = src.current_fragment_mut();

            frag_mut.start = new_start;
            frag_mut.len = frag.len - prev_len;
            frag_mut.content_start = new_content_start;
            break;
        }
    }
    offset
}

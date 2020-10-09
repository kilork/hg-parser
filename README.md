# hg-parser

Mercurial repository parser written in the [Rust programming language](https://www.rust-lang.org/en-US/).

## Basic usage

### Add dependency to Cargo.toml

```toml
[dependencies]
hg-parser = "0.4"
```

### Use case - Analyse revision log and export to ```git fast-import``` format

```rust
use hg_parser::{file_content, FileType, ManifestEntryDetails, MercurialRepository, Revision};

use std::env::args;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::string::ParseError;
use std::time::Instant;

fn main() -> Result<(), Error> {
    let path: PathBuf = args().nth(1).expect("path not provided").parse()?;
    export_repo(path)
}

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

## Implementation details

**hg-parser** is based on repository parse code from [mononoke](https://github.com/facebookexperimental/mononoke) project. Which basically based on original Mercurial source code. Version has some simplifications which may not work for you.
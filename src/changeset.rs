use crate::error::ErrorKind;
use crate::manifest::ManifestEntry;
use crate::types::{DateTime, NodeHash, Revision, RevisionLogEntry};
use std::collections::HashMap;
use std::fmt::Debug;
use std::sync::Arc;
use std::{fmt, str};

pub struct ChangesetHeader {
    pub p1: Option<Revision>,
    pub p2: Option<Revision>,
    pub manifestid: NodeHash,
    pub user: Vec<u8>,
    pub time: DateTime,
    pub extra: HashMap<Vec<u8>, Vec<u8>>,
    pub files: Vec<Vec<u8>>,
    pub comment: Vec<u8>,
}

impl Debug for ChangesetHeader {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        writeln!(
            fmt,
            "ChangesetHeader(\np1:{:?}\np2:{:?}\nmanifestid:{}\nuser:{}\ntime:{:?}\nextra:{}\nfiles:\n{}\ncomment:\n{}\n)",
            self.p1,
            self.p2,
            self.manifestid,
            str::from_utf8(&self.user).expect("bad user utf8"),
            self.time,
            self.extra
                .iter()
                .map(|(key, value)| format!(
                    "{}:{}",
                    str::from_utf8(&key).expect("bad extra key utf8"),
                    str::from_utf8(&value).unwrap_or("bad extra value utf8")
                ))
                .collect::<Vec<_>>()
                .join(","),
                self.files.iter().map(|key| format!(
                    "{}",
                    str::from_utf8(&key).unwrap()
                )).collect::<Vec<_>>().join("\n"),
            str::from_utf8(&self.comment).expect("bad comment utf8"),
        )
    }
}
impl ChangesetHeader {
    pub fn from_entry_bytes(entry: &RevisionLogEntry, data: &[u8]) -> Result<Self, ErrorKind> {
        let mut lines = data.split(|&x| x == b'\n');
        if let (Some(manifestid), Some(user), Some(timeextra)) = (
            lines
                .next()
                .and_then(|x| str::from_utf8(x).ok())
                .and_then(|x| x.parse().ok()),
            lines.next(),
            lines.next(),
        ) {
            let mut parts = timeextra.splitn(3, |&x| x == b' ');

            if let (Some(time), Some(tz), extra) = (
                parts
                    .next()
                    .and_then(|x| str::from_utf8(x).ok())
                    .and_then(|x| x.parse().ok()),
                parts
                    .next()
                    .and_then(|x| str::from_utf8(x).ok())
                    .and_then(|x| x.parse().ok()),
                parts.next(),
            ) {
                let mut files = Vec::new();
                while let Some(file) = lines.next() {
                    if file.is_empty() {
                        break;
                    }
                    files.push(file.into());
                }
                Ok(ChangesetHeader {
                    p1: entry.p1.clone(),
                    p2: entry.p2.clone(),
                    manifestid,
                    user: user.into(),
                    time: DateTime::from_timestamp(time, tz)?,
                    extra: extra
                        .map(|x| {
                            x.split(|&y| y == 0)
                                .filter_map(|y| {
                                    let mut z = y.splitn(2, |&k| k == b':');
                                    if let (Some(key), Some(value)) =
                                        (z.next().map(unescape), z.next().map(unescape))
                                    {
                                        Some((key, value))
                                    } else {
                                        None
                                    }
                                })
                                .collect()
                        })
                        .unwrap_or_else(HashMap::new),
                    files,
                    comment: lines.collect::<Vec<_>>().join(&b'\n'),
                })
            } else {
                Err(ErrorKind::Parser)
            }
        } else {
            Err(ErrorKind::Parser)
        }
    }
}

fn unescape<'a, S: IntoIterator<Item = &'a u8>>(s: S) -> Vec<u8> {
    let mut ret = Vec::new();
    let mut quote = false;

    for c in s.into_iter() {
        match *c {
            b'0' if quote => {
                quote = false;
                ret.push(b'\0');
            }
            b'n' if quote => {
                quote = false;
                ret.push(b'\n');
            }
            b'r' if quote => {
                quote = false;
                ret.push(b'\r');
            }
            b'\\' if quote => {
                quote = false;
                ret.push(b'\\');
            }
            c if quote => {
                quote = false;
                ret.push(b'\\');
                ret.push(c)
            }
            b'\\' => {
                assert!(!quote);
                quote = true;
            }
            c => {
                quote = false;
                ret.push(c);
            }
        }
    }

    ret
}

#[derive(Debug)]
pub struct Changeset {
    pub revision: Revision,
    pub header: ChangesetHeader,
    pub files: Vec<ChangesetFile>,
}

#[derive(Debug)]
pub struct ChangesetFile {
    pub path: Vec<u8>,
    pub data: Option<Arc<Vec<u8>>>,
    pub manifest_entry: Option<ManifestEntry>,
}

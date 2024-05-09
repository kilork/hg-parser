use std::{
    collections::BTreeMap,
    fmt::{self, Debug},
    str,
    sync::Arc,
};

use crate::{error::ErrorKind, types::NodeHash};

pub(crate) struct Manifest {
    pub files: BTreeMap<Vec<u8>, ManifestEntry>,
}

impl Debug for Manifest {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(
            fmt,
            "Manifest(\nfiles:\n{}\n)",
            self.files
                .iter()
                .map(|(key, value)| format!("{}: {:?}", str::from_utf8(key).unwrap(), value))
                .collect::<Vec<_>>()
                .join("\n")
        )
    }
}

/// Manifest entry for file. Contains revision hash and file metainformation.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct ManifestEntry {
    pub id: NodeHash,
    pub details: ManifestEntryDetails,
}

impl ManifestEntry {
    fn parse(data: &[u8]) -> Result<ManifestEntry, ErrorKind> {
        let (hash, flags) = data.split_at(40);
        let id: NodeHash = str::from_utf8(hash).unwrap().parse().unwrap();

        let details = if flags.is_empty() {
            ManifestEntryDetails::File(FileType::Regular)
        } else {
            match flags[0] {
                b'l' => ManifestEntryDetails::File(FileType::Symlink),
                b'x' => ManifestEntryDetails::File(FileType::Executable),
                b't' => ManifestEntryDetails::Tree,
                unk => return Err(ErrorKind::Manifest(format!("Unknown flag {}", unk))),
            }
        };

        Ok(ManifestEntry { id, details })
    }
}

impl From<Arc<[u8]>> for Manifest {
    fn from(value: Arc<[u8]>) -> Self {
        let mut files = BTreeMap::new();
        for line in value.split(|&x| x == b'\n') {
            if line.is_empty() {
                break;
            }
            let mut parts = line.splitn(2, |&x| x == 0);
            if let (Some(file), Some(rest)) = (parts.next(), parts.next()) {
                files.insert(file.into(), ManifestEntry::parse(rest).unwrap());
            } else {
                panic!("wrong manifest line");
            }
        }
        Manifest { files }
    }
}

/// File meta information.
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub enum ManifestEntryDetails {
    File(FileType),
    Tree,
}

impl fmt::Display for ManifestEntryDetails {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ManifestEntryDetails::Tree => write!(f, "tree"),
            ManifestEntryDetails::File(ft) => write!(f, "{}", ft),
        }
    }
}

/// File type. Can be regular, executable, or symlink.
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum FileType {
    Regular,
    Executable,
    Symlink,
}

impl fmt::Display for FileType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let s = match self {
            FileType::Symlink => "symlink",
            FileType::Executable => "executable",
            FileType::Regular => "regular",
        };
        write!(f, "{}", s)
    }
}

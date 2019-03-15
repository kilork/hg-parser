use super::error::ErrorKind;
use bitflags::bitflags;
use chrono::{
    DateTime as ChronoDateTime, FixedOffset, Local, LocalResult, NaiveDateTime, TimeZone,
};
use crypto::{digest::Digest, sha1};
use std::fmt::Debug;
use std::fmt::{self, Display};
use std::ops::Add;
use std::ops::Range;
use std::ops::Sub;
use std::str::FromStr;

/// Repository requires flags.
/// Repositories contain a file (``.hg/requires``) containing a list of
/// features/capabilities that are *required* for clients to interface
/// with the repository.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub(crate) enum RepositoryRequire {
    /// When present, revlogs are version 1 (**RevlogNG**).
    Revlogv1,
    /// The **store** repository layout is used.
    Store,
    /// The **fncache** layout hash encodes filenames with long paths and encodes reserved filenames.
    FnCache,
    /// Denotes that the store for a repository is shared from another location (defined by the ``.hg/sharedpath`` file).
    Shared,
    /// Derivative of ``shared``; the location of the store is relative to the store of this repository.
    RelShared,
    /// The *dotencode* layout encodes the first period or space in filenames to prevent issues on OS X and Windows.
    DotEncode,
    /// Denotes a revlog delta encoding format that was experimental and
    /// replaced by *generaldelta*. It should not be seen in the wild because
    /// it was never enabled by default.
    ParentDelta,
    /// Revlogs should be created with the *generaldelta* flag enabled. The
    /// generaldelta flag will cause deltas to be encoded against a parent
    /// revision instead of the previous revision in the revlog.
    GeneralDelta,
    /// Denotes that version 2 of manifests are being used.
    Manifestv2,
    /// Denotes that tree manifests are being used. Tree manifests are
    /// one manifest per directory (as opposed to a single flat manifest).
    TreeManifest,
    /// The working directory is sparse (only contains a subset of files).
    ExpSparse,
}

impl FromStr for RepositoryRequire {
    type Err = ErrorKind;

    fn from_str(value: &str) -> Result<RepositoryRequire, ErrorKind> {
        use RepositoryRequire::*;
        match value {
            "revlogv1" => Ok(Revlogv1),
            "store" => Ok(Store),
            "fncache" => Ok(FnCache),
            "shared" => Ok(Shared),
            "relshared" => Ok(RelShared),
            "dotencode" => Ok(DotEncode),
            "parentdelta" => Ok(ParentDelta),
            "generaldelta" => Ok(GeneralDelta),
            "manifestv2" => Ok(Manifestv2),
            "treemanifest" => Ok(TreeManifest),
            "exp-sparse" => Ok(ExpSparse),
            other => Err(ErrorKind::UnknownRequirement(other.into())),
        }
    }
}

/// Mercurial revision's index.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct Revision(pub u32);

impl Revision {
    /// Return iterator for a range from index to `lim`.
    pub fn range_to(&self, lim: Self) -> RevisionRange {
        RevisionRange(self.0, lim.0)
    }

    /// Return an open ended iterator from index.
    pub fn range(&self) -> RevisionRange {
        RevisionRange(self.0, std::u32::MAX)
    }
}

impl From<u32> for Revision {
    fn from(value: u32) -> Self {
        Self(value)
    }
}

impl Add<u32> for Revision {
    type Output = Self;

    fn add(self, other: u32) -> Self {
        Self(self.0 + other)
    }
}

impl Sub<u32> for Revision {
    type Output = Self;

    fn sub(self, other: u32) -> Self {
        assert!(self.0 >= other);
        Self(self.0 - other)
    }
}

impl From<Revision> for usize {
    fn from(value: Revision) -> usize {
        value.0 as usize
    }
}

/// Convert a `Revision` into an iterator of `Revision` values
/// starting at `Revision`'s value. ie, `Revision`(2).into_iter() => `Revision`(2), `Revision`(3), ...
impl<'a> IntoIterator for &'a Revision {
    type Item = Revision;
    type IntoIter = RevisionRange;

    fn into_iter(self) -> Self::IntoIter {
        self.range()
    }
}

/// An iterator over a range of `Revision`.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct RevisionRange(u32, u32);

impl Iterator for RevisionRange {
    type Item = Revision;

    fn next(&mut self) -> Option<Self::Item> {
        if self.0 < self.1 {
            let ret = Revision(self.0);
            self.0 += 1;
            Some(ret)
        } else {
            None
        }
    }
}

impl DoubleEndedIterator for RevisionRange {
    fn next_back(&mut self) -> Option<Revision> {
        if self.0 < self.1 {
            self.1 -= 1;
            let ret = Revision(self.1);
            Some(ret)
        } else {
            None
        }
    }
}

impl From<Range<usize>> for RevisionRange {
    fn from(value: Range<usize>) -> Self {
        Self(value.start as u32, value.end as u32)
    }
}

/// `Revlog` version number
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Version {
    Revlog0 = 0,
    RevlogNG = 1,
}

/// `Revlog` features
bitflags! {
    pub struct Features: u16 {
        const INLINE        = 1 << 0;
        const GENERAL_DELTA = 1 << 1;
    }
}

/// Per-revision flags
bitflags! {
    pub struct IdxFlags: u16 {
        const EXTSTORED     = 1 << 13;
        const CENSORED      = 1 << 15;
    }
}

/// `Revlog` header
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct RevisionLogHeader {
    pub version: Version,
    pub features: Features,
}

#[derive(Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct NodeHash([u8; 20]);

const HEX_CHARS: &[u8] = b"0123456789abcdef";

impl NodeHash {
    pub fn to_hex(&self) -> String {
        let mut v = Vec::with_capacity(40);
        for &byte in &self.0 {
            v.push(HEX_CHARS[(byte >> 4) as usize]);
            v.push(HEX_CHARS[(byte & 0xf) as usize]);
        }

        unsafe { String::from_utf8_unchecked(v) }
    }

    pub fn from_slice(data: &[u8]) -> Self {
        let mut sha1 = sha1::Sha1::new();
        sha1.input(data);

        let mut ret = NULL;
        sha1.result(&mut ret.0[..]);
        ret
    }
}

pub const NULL: NodeHash = NodeHash([0; 20]);

impl AsRef<[u8]> for NodeHash {
    fn as_ref(&self) -> &[u8] {
        &self.0[..]
    }
}

impl Display for NodeHash {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        Display::fmt(&self.to_hex(), fmt)
    }
}

impl Debug for NodeHash {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "NodeHash({})", self)
    }
}

impl<'a> From<&'a [u8]> for NodeHash {
    fn from(value: &'a [u8]) -> Self {
        let mut data: [u8; 20] = Default::default();
        data.copy_from_slice(value);
        Self(data)
    }
}

impl FromStr for NodeHash {
    type Err = ErrorKind;

    fn from_str(s: &str) -> Result<Self, ErrorKind> {
        let mut ret = Self([0; 20]);

        for idx in 0..ret.0.len() {
            ret.0[idx] = match u8::from_str_radix(&s[(idx * 2)..(idx * 2 + 2)], 16) {
                Ok(v) => v,
                Err(_) => return Err(ErrorKind::Parser),
            }
        }

        Ok(ret)
    }
}

/// Entry entry for a revision
#[derive(Copy, Clone, Debug)]
pub struct RevisionLogEntry {
    pub offset: u64,         // offset of content (delta/literal) in datafile (or inlined)
    pub flags: IdxFlags,     // unused?
    pub compressed_len: u32, // compressed content size
    pub len: Option<u32>,    // size of final file (after applying deltas)
    pub baserev: Option<Revision>, // base/previous rev for deltas (None if literal)
    pub linkrev: Revision,   // changeset id
    pub p1: Option<Revision>, // parent p1
    pub p2: Option<Revision>, // parent p2
    pub nodeid: NodeHash,    // nodeid
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct Delta {
    // Fragments should be in sorted order by start offset and should not overlap.
    pub(crate) fragments: Vec<Fragment>,
}

impl Delta {
    /// Construct a new Delta object. Verify that `frags` is sane, sorted and
    /// non-overlapping.
    pub fn new(fragments: Vec<Fragment>) -> Result<Self, ErrorKind> {
        Ok(Delta { fragments })
    }
    pub fn fragments(&self) -> &[Fragment] {
        self.fragments.as_slice()
    }
}
/// Represents a single contiguous modified region of text.
#[derive(Clone, Eq, PartialEq, Ord, PartialOrd)]
pub struct Fragment {
    pub start: usize,
    pub end: usize,
    pub content: Vec<u8>,
}

impl Fragment {
    // Return the length of the content
    pub fn content_length(&self) -> usize {
        self.content.len()
    }
}

impl Debug for Fragment {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(
            fmt,
            "Fragment(\nstart:{}\nend:{}\ncontent:{:?}\n)",
            self.start,
            self.end,
            std::str::from_utf8(&self.content)
        )
    }
}

#[derive(Debug, Clone)]
pub enum Chunk {
    /// Literal text of the revision
    Literal(Vec<u8>),
    /// Vector of `Delta`s against a previous version
    Deltas(Delta),
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct DateTime(ChronoDateTime<FixedOffset>);

impl DateTime {
    #[inline]
    pub fn new(dt: ChronoDateTime<FixedOffset>) -> Self {
        DateTime(dt)
    }

    pub fn now() -> Self {
        let now = Local::now();
        DateTime(now.with_timezone(now.offset()))
    }

    pub fn from_timestamp(secs: i64, tz_offset_secs: i32) -> Result<Self, ErrorKind> {
        let tz = FixedOffset::west_opt(tz_offset_secs).ok_or_else(|| {
            ErrorKind::InvalidDateTime(format!("timezone offset out of range: {}", tz_offset_secs))
        })?;
        let dt = match tz.timestamp_opt(secs, 0) {
            LocalResult::Single(dt) => dt,
            _ => {
                return Err(ErrorKind::InvalidDateTime(format!(
                    "seconds out of range: {}",
                    secs
                )));
            }
        };
        Ok(Self::new(dt))
    }

    /// Construct a new `DateTime` from an RFC3339 string.
    ///
    /// RFC3339 is a standardized way to represent a specific moment in time. See
    /// https://tools.ietf.org/html/rfc3339.
    pub fn from_rfc3339(rfc3339: &str) -> Result<Self, ErrorKind> {
        let dt = ChronoDateTime::parse_from_rfc3339(rfc3339)?;
        Ok(Self::new(dt))
    }

    /// Retrieves the Unix timestamp in UTC.
    #[inline]
    pub fn timestamp_secs(&self) -> i64 {
        self.0.timestamp()
    }

    /// Retrieves the timezone offset, as represented by the number of seconds to
    /// add to convert local time to UTC.
    #[inline]
    pub fn tz_offset_secs(&self) -> i32 {
        // This is the same as the way Mercurial stores timezone offsets.
        self.0.offset().utc_minus_local()
    }

    #[inline]
    pub fn as_chrono(&self) -> &ChronoDateTime<FixedOffset> {
        &self.0
    }

    #[inline]
    pub fn into_chrono(self) -> ChronoDateTime<FixedOffset> {
        self.0
    }
}

impl Display for DateTime {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "{}", self.0)
    }
}

/// Number of non-leap-nanoseconds since January 1, 1970 UTC
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct Timestamp(i64);

impl Timestamp {
    pub fn now() -> Self {
        DateTime::now().into()
    }

    pub fn from_timestamp_nanos(ts: i64) -> Self {
        Timestamp(ts)
    }

    pub fn timestamp_nanos(&self) -> i64 {
        self.0
    }
}

impl From<DateTime> for Timestamp {
    fn from(dt: DateTime) -> Self {
        Timestamp(dt.0.timestamp_nanos())
    }
}

impl From<Timestamp> for DateTime {
    fn from(ts: Timestamp) -> Self {
        let ts_secs = ts.0 / 1_000_000_000;
        let ts_nsecs = (ts.0 % 1_000_000_000) as u32;
        DateTime::new(ChronoDateTime::<FixedOffset>::from_utc(
            NaiveDateTime::from_timestamp(ts_secs, ts_nsecs),
            FixedOffset::west(0),
        ))
    }
}

pub struct MercurialTag {
    pub node: NodeHash,
    pub name: String,
}

impl FromStr for MercurialTag {
    type Err = ErrorKind;

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        let mut parts = value.split_whitespace();
        if let (Some(node), Some(name)) = (
            parts
                .next()
                .and_then(|x| if x.len() == 40 { Some(x) } else { None })
                .and_then(|x| x.parse().ok()),
            parts.next().map(String::from),
        ) {
            Ok(Self { node, name })
        } else {
            Err(ErrorKind::Parser)
        }
    }
}

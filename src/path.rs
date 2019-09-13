use std::cmp;
use std::convert::From;
use std::ffi::OsStr;
use std::fmt::{self, Display};
use std::io::{self, Write};
use std::iter::{once, Once};
#[cfg(any(unix, target_os = "redox"))]
use std::os::unix::ffi::OsStrExt;
use std::path::PathBuf;
use std::slice::Iter;
use std::vec::IntoIter;

use crate::error::ErrorKind;
use crate::types::*;

use lazy_static::lazy_static;

lazy_static! {
    pub static ref DOT: MPathElement = MPathElement(b".".to_vec());
    pub static ref DOTDOT: MPathElement = MPathElement(b"..".to_vec());
}

#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct MPathElement(Vec<u8>);

impl MPathElement {
    #[inline]
    pub fn new(element: Vec<u8>) -> Result<MPathElement, ErrorKind> {
        Ok(MPathElement(element))
    }

    #[inline]
    pub fn as_bytes(&self) -> &[u8] {
        self.0.as_slice()
    }

    #[inline]
    pub fn to_bytes(&self) -> Vec<u8> {
        self.0.clone()
    }

    pub fn extend(&mut self, toappend: &[u8]) {
        self.0.extend(toappend.iter());
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.0.len()
    }
}

impl From<MPathElement> for MPath {
    fn from(element: MPathElement) -> Self {
        MPath {
            elements: vec![element],
        }
    }
}

#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct MPath {
    elements: Vec<MPathElement>,
}

impl MPath {
    pub fn new<P: AsRef<[u8]>>(p: P) -> Result<MPath, ErrorKind> {
        let p = p.as_ref();
        let elements: Vec<_> = p
            .split(|c| *c == b'/')
            .filter(|e| !e.is_empty())
            .map(|e| {
                // These instances have already been checked to contain null bytes and also
                // are split on '/' bytes and non-empty, so they're valid by construction. Skip the
                // verification in MPathElement::new.
                MPathElement(e.into())
            })
            .collect();
        if elements.is_empty() {
            return Err(ErrorKind::InvalidPath(format!(
                "{} path cannot be empty",
                String::from_utf8_lossy(p).into_owned(),
            )));
        }
        Ok(MPath { elements })
    }

    pub fn join<'a, Elements: IntoIterator<Item = &'a MPathElement>>(
        &self,
        another: Elements,
    ) -> MPath {
        let mut newelements = self.elements.clone();
        newelements.extend(
            another
                .into_iter()
                .filter(|elem| !elem.0.is_empty())
                .cloned(),
        );
        MPath {
            elements: newelements,
        }
    }

    pub fn join_element(&self, element: Option<&MPathElement>) -> MPath {
        match element {
            Some(element) => self.join(element),
            None => self.clone(),
        }
    }

    pub fn join_opt<'a, Elements: IntoIterator<Item = &'a MPathElement>>(
        path: Option<&Self>,
        another: Elements,
    ) -> Option<Self> {
        match path {
            Some(path) => Some(path.join(another)),
            None => {
                let elements: Vec<MPathElement> = another
                    .into_iter()
                    .filter(|elem| !elem.0.is_empty())
                    .cloned()
                    .collect();
                if elements.is_empty() {
                    None
                } else {
                    Some(MPath { elements })
                }
            }
        }
    }

    pub fn join_opt_element(path: Option<&Self>, element: &MPathElement) -> Self {
        match path {
            Some(path) => path.join_element(Some(element)),
            None => MPath {
                elements: vec![element.clone()],
            },
        }
    }

    pub fn join_element_opt(path: Option<&Self>, element: Option<&MPathElement>) -> Option<Self> {
        match element {
            Some(element) => Self::join_opt(path, element),
            None => path.cloned(),
        }
    }

    pub fn iter_opt(path: Option<&Self>) -> Iter<MPathElement> {
        match path {
            Some(path) => path.into_iter(),
            None => [].iter(),
        }
    }

    pub fn vec_iter_opt(path: Option<Self>) -> IntoIter<MPathElement> {
        match path {
            Some(path) => path.into_iter(),
            None => (vec![]).into_iter(),
        }
    }

    /// The number of components in this path.
    pub fn num_components(&self) -> usize {
        self.elements.len()
    }

    /// The number of leading components that are common.
    pub fn common_components<'a, E: IntoIterator<Item = &'a MPathElement>>(
        &self,
        other: E,
    ) -> usize {
        self.elements
            .iter()
            .zip(other)
            .take_while(|&(e1, e2)| e1 == e2)
            .count()
    }

    /// Whether this path is a path prefix of the given path.
    /// `foo` is a prefix of `foo/bar`, but not of `foo1`.
    #[inline]
    pub fn is_prefix_of<'a, E: IntoIterator<Item = &'a MPathElement>>(&self, other: E) -> bool {
        self.common_components(other.into_iter()) == self.num_components()
    }

    /// The final component of this path.
    pub fn basename(&self) -> &MPathElement {
        self.elements
            .last()
            .expect("MPaths have at least one component")
    }

    /// Create a new path with the number of leading components specified.
    pub fn take_prefix_components(&self, components: usize) -> Result<Option<MPath>, ErrorKind> {
        match components {
            0 => Ok(None),
            x if x > self.num_components() => Err(ErrorKind::InvalidPath(format!(
                "taking {} components but path only has {}",
                components,
                self.num_components()
            ))),
            _ => Ok(Some(MPath {
                elements: self.elements[..components].to_vec(),
            })),
        }
    }

    pub fn generate<W: Write>(&self, out: &mut W) -> io::Result<()> {
        out.write_all(&self.to_vec())
    }

    pub fn to_vec(&self) -> Vec<u8> {
        let ret: Vec<_> = self.elements.iter().map(|e| e.0.as_ref()).collect();
        ret.join(&b'/')
    }

    /// The length of this path, including any slashes in it.
    pub fn len(&self) -> usize {
        // n elements means n-1 slashes
        let slashes = self.elements.len() - 1;
        let elem_len: usize = self.elements.iter().map(|elem| elem.len()).sum();
        slashes + elem_len
    }

    // Private because it does not validate elements - you must ensure that it's non-empty
    fn from_elements<'a, I>(elements: I) -> Self
    where
        I: Iterator<Item = &'a MPathElement>,
    {
        Self {
            elements: elements.cloned().collect(),
        }
    }

    /// Split an MPath into dirname (if possible) and file name
    pub fn split_dirname(&self) -> (Option<MPath>, &MPathElement) {
        let (filename, dirname_elements) = self
            .elements
            .split_last()
            .expect("MPaths should never be empty");

        if dirname_elements.is_empty() {
            (None, filename)
        } else {
            (
                Some(MPath::from_elements(dirname_elements.iter())),
                filename,
            )
        }
    }

    pub fn display_opt(path_opt: Option<&MPath>) -> DisplayOpt<'_> {
        DisplayOpt(path_opt)
    }
}

pub struct DisplayOpt<'a>(Option<&'a MPath>);

impl<'a> Display for DisplayOpt<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.0 {
            Some(path) => write!(f, "{}", path),
            None => write!(f, "(none)"),
        }
    }
}

impl IntoIterator for MPath {
    type Item = MPathElement;
    type IntoIter = ::std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.elements.into_iter()
    }
}

impl<'a> IntoIterator for &'a MPath {
    type Item = &'a MPathElement;
    type IntoIter = Iter<'a, MPathElement>;

    fn into_iter(self) -> Self::IntoIter {
        self.elements.iter()
    }
}

impl<'a> IntoIterator for &'a MPathElement {
    type Item = &'a MPathElement;
    type IntoIter = Once<&'a MPathElement>;

    fn into_iter(self) -> Self::IntoIter {
        once(self)
    }
}

impl<'a> From<&'a MPath> for Vec<u8> {
    fn from(path: &MPath) -> Self {
        path.to_vec()
    }
}

impl<'a> From<&'a [u8]> for MPath {
    fn from(value: &[u8]) -> Self {
        MPath::new(value).unwrap()
    }
}

impl<'a> From<&'a str> for MPath {
    fn from(value: &str) -> Self {
        MPath::new(value.as_bytes()).unwrap()
    }
}

lazy_static! {
    static ref COMPONENT_CHARS: Vec<u8> = (2..b'\n')
        .chain((b'\n' + 1)..b'/')
        .chain((b'/' + 1)..255)
        .collect();
}

impl Display for MPath {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "{}", String::from_utf8_lossy(&self.to_vec()))
    }
}

// Implement our own Debug so that strings are displayed properly
impl fmt::Debug for MPathElement {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(
            fmt,
            "MPathElement(\"{}\")",
            String::from_utf8_lossy(&self.0)
        )
    }
}

impl fmt::Debug for MPath {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "MPath(\"{}\")", self)
    }
}

fn fsencode_filter<P: AsRef<[u8]>>(p: P, dotencode: bool) -> String {
    let p = p.as_ref();
    let p = fnencode(p, true);
    let p = auxencode(p, dotencode);
    String::from_utf8(p).expect("bad utf8")
}

fn fsencode_dir_impl<'a, Iter>(dotencode: bool, iter: Iter) -> PathBuf
where
    Iter: Iterator<Item = &'a MPathElement>,
{
    iter.map(|p| fsencode_filter(direncode(p.as_bytes()), dotencode))
        .collect()
}

const MAXSTOREPATHLEN: usize = 120;

/// Perform the mapping to a filesystem path used in a .hg directory
/// Assumes that this path is a file.
/// This encoding is used when both 'store' and 'fncache' requirements are in the repo.
pub fn fncache_fsencode(elements: &[MPathElement], dotencode: bool) -> PathBuf {
    let mut path = elements.iter().rev();
    let file = path.next();
    let path = path.rev();
    let mut ret: PathBuf = fsencode_dir_impl(dotencode, path.clone());

    if let Some(basename) = file {
        ret.push(fsencode_filter(basename.as_bytes(), dotencode));
        let os_str: &OsStr = ret.as_ref();

        #[cfg(any(unix, target_os = "redox"))]
        let os_str_len = os_str.as_bytes().len();
        #[cfg(windows)]
        let os_str_len = os_str.len(); // need to know more about windows path lengths

        if os_str_len > MAXSTOREPATHLEN {
            hashencode(
                path.map(|elem| elem.to_bytes()).collect(),
                basename.as_bytes(),
                dotencode,
            )
        } else {
            ret.clone()
        }
    } else {
        PathBuf::new()
    }
}

/// Perform the mapping to a filesystem path used in a .hg directory
/// Assumes that this path is a file.
/// This encoding is used when 'store' requirement is present in the repo, but 'fncache'
/// requirement is not present.
pub fn simple_fsencode(elements: &[MPathElement]) -> PathBuf {
    let mut path = elements.iter().rev();
    let file = path.next();
    let directory_elements = path.rev();

    if let Some(basename) = file {
        let encoded_directory: PathBuf = directory_elements
            .map(|elem| {
                let encoded_element = fnencode(direncode(elem.as_bytes()), false);
                String::from_utf8(encoded_element).expect("bad utf8")
            })
            .collect();

        let encoded_basename = PathBuf::from(
            String::from_utf8(fnencode(basename.as_bytes(), false)).expect("bad utf8"),
        );
        encoded_directory.join(encoded_basename)
    } else {
        PathBuf::new()
    }
}

static HEX: &[u8] = b"0123456789abcdef";

fn hexenc(byte: u8, out: &mut Vec<u8>) {
    out.push(b'~');
    out.push(HEX[((byte >> 4) & 0xf) as usize]);
    out.push(HEX[(byte & 0xf) as usize]);
}

// Encode directory names
fn direncode(elem: &[u8]) -> Vec<u8> {
    let mut ret = Vec::new();

    ret.extend_from_slice(elem);
    if elem.ends_with(b".hg") || elem.ends_with(b".i") || elem.ends_with(b".d") {
        ret.extend_from_slice(b".hg")
    }

    ret
}

// If this is not for fncache then path elements longer than 255 in this encoding will not use
// UPPERCASE -> _lowercase encoding, as per D8527475
// If this is not for fncache and previous encoding scheme result in longer then 255
// _(underscore) -> :(semicolon), as per D9967059
fn fnencode<E: AsRef<[u8]>>(elem: E, forfncache: bool) -> Vec<u8> {
    enum UnderscoreEncoding {
        EncodeTo(&'static [u8]),
    }

    enum UpperEncoding {
        ToUnderscoreAndLower,
        ToUpper,
    }

    fn upper_to_underscore_and_lower(ret: &mut Vec<u8>, e: u8) {
        ret.push(b'_');
        ret.push(e - b'A' + b'a');
    }

    fn upper_to_upper(ret: &mut Vec<u8>, e: u8) {
        ret.push(e);
    }

    fn fnencode_internal(
        elem: &[u8],
        encode_upper: UpperEncoding,
        encode_underscore: UnderscoreEncoding,
    ) -> Vec<u8> {
        let mut ret = Vec::new();

        for e in elem {
            let e = *e;
            match e {
                0..=31 | 126..=255 => hexenc(e, &mut ret),
                b'\\' | b':' | b'*' | b'?' | b'"' | b'<' | b'>' | b'|' => hexenc(e, &mut ret),
                b'A'..=b'Z' => match encode_upper {
                    UpperEncoding::ToUnderscoreAndLower => {
                        upper_to_underscore_and_lower(&mut ret, e)
                    }
                    UpperEncoding::ToUpper => upper_to_upper(&mut ret, e),
                },
                b'_' => match encode_underscore {
                    UnderscoreEncoding::EncodeTo(slice) => ret.extend_from_slice(&slice),
                },
                _ => ret.push(e),
            }
        }

        ret
    }

    let elem = elem.as_ref();
    let ret = fnencode_internal(
        elem,
        UpperEncoding::ToUnderscoreAndLower,
        UnderscoreEncoding::EncodeTo(b"__"),
    );

    if !forfncache && ret.len() > 255 {
        let encoded_upper = fnencode_internal(
            elem,
            UpperEncoding::ToUpper,
            UnderscoreEncoding::EncodeTo(b"__"),
        );
        if encoded_upper.len() > 255 {
            fnencode_internal(
                elem,
                UpperEncoding::ToUpper,
                UnderscoreEncoding::EncodeTo(b":"),
            )
        } else {
            encoded_upper
        }
    } else {
        ret
    }
}

fn lowerencode(elem: &[u8]) -> Vec<u8> {
    let mut ret = Vec::new();

    for e in elem {
        let e = *e;
        match e {
            0..=31 | 126..=255 => hexenc(e, &mut ret),
            b'\\' | b':' | b'*' | b'?' | b'"' | b'<' | b'>' | b'|' => hexenc(e, &mut ret),
            b'A'..=b'Z' => {
                ret.push(e - b'A' + b'a');
            }
            _ => ret.push(e),
        }
    }

    ret
}

// if path element is a reserved windows name, remap last character to ~XX
fn auxencode<E: AsRef<[u8]>>(elem: E, dotencode: bool) -> Vec<u8> {
    let elem = elem.as_ref();
    let mut ret = Vec::new();

    if let Some((first, elements)) = elem.split_first() {
        if dotencode && (first == &b'.' || first == &b' ') {
            hexenc(*first, &mut ret);
            ret.extend_from_slice(elements);
        } else {
            // if base portion of name is a windows reserved name,
            // then hex encode 3rd char
            let pos = elem
                .iter()
                .position(|c| *c == b'.')
                .unwrap_or_else(|| elem.len());
            let prefix_len = ::std::cmp::min(3, pos);
            match &elem[..prefix_len] {
                b"aux" | b"con" | b"prn" | b"nul" if pos == 3 => {
                    ret.extend_from_slice(&elem[..2]);
                    hexenc(elem[2], &mut ret);
                    ret.extend_from_slice(&elem[3..]);
                }
                b"com" | b"lpt" if pos == 4 && elem[3] >= b'1' && elem[3] <= b'9' => {
                    ret.extend_from_slice(&elem[..2]);
                    hexenc(elem[2], &mut ret);
                    ret.extend_from_slice(&elem[3..]);
                }
                _ => ret.extend_from_slice(elem),
            }
        }
    }
    // hex encode trailing '.' or ' '
    if let Some(last) = ret.pop() {
        if last == b'.' || last == b' ' {
            hexenc(last, &mut ret);
        } else {
            ret.push(last);
        }
    }

    ret
}

fn get_extension(basename: &[u8]) -> &[u8] {
    let idx = basename
        .iter()
        .enumerate()
        .rev()
        .find(|&(_, c)| *c == b'.')
        .map(|(idx, _)| idx);
    match idx {
        None | Some(0) => b"",
        Some(idx) => &basename[idx..],
    }
}

fn hashed_file(dirs: &[Vec<u8>], file: &[u8]) -> NodeHash {
    let mut elements: Vec<_> = dirs.iter().map(|elem| direncode(&elem)).collect();
    elements.push(Vec::from(file));

    NodeHash::from_slice(elements.join(&b'/').as_ref())
}

/// This function emulates core mercurial _hashencode() function. In core mercurial it is used
/// if path is longer than MAXSTOREPATHLEN.
/// Resulting path starts with "dh/" prefix, it has the same extension as initial file, and it
/// also contains sha-1 hash of the initial file.
/// Each path element is encoded to avoid file name collisions, and they are combined
/// in such way that resulting path is shorter than MAXSTOREPATHLEN.
fn hashencode(dirs: Vec<Vec<u8>>, file: &[u8], dotencode: bool) -> PathBuf {
    let sha1 = hashed_file(&dirs, file);

    let mut parts = dirs
        .iter()
        .map(|elem| direncode(&elem))
        .map(|elem| lowerencode(&elem))
        .map(|elem| auxencode(elem, dotencode));

    let mut shortdirs = Vec::new();
    // Prefix (which is usually 'data' or 'meta') is replaced with 'dh'.
    // Other directories will be converted.
    let prefix = parts.next();
    let prefix_len = prefix.map(|elem| elem.len()).unwrap_or(0);
    // Each directory is no longer than `dirprefixlen`, and total length is less than
    // `maxshortdirslen`. These constants are copied from core mercurial code.
    let dirprefixlen = 8;
    let maxshortdirslen = 8 * (dirprefixlen + 1) - prefix_len;
    let mut shortdirslen = 0;
    for p in parts {
        let size = cmp::min(dirprefixlen, p.len());
        let dir = &p[..size];
        let dir = match dir.split_last() {
            Some((last, prefix)) => {
                if last == &b'.' || last == &b' ' {
                    let mut vec = Vec::from(prefix);
                    vec.push(b'_');
                    vec
                } else {
                    Vec::from(dir)
                }
            }
            _ => Vec::from(dir),
        };

        if shortdirslen == 0 {
            shortdirslen = dir.len();
        } else {
            // 1 is for '/'
            let t = shortdirslen + 1 + dir.len();
            if t > maxshortdirslen {
                break;
            }
            shortdirslen = t;
        }
        shortdirs.push(dir);
    }
    let mut shortdirs = shortdirs.join(&b'/');
    if !shortdirs.is_empty() {
        shortdirs.push(b'/');
    }

    // File name encoding is a bit different from directory element encoding - direncode() is not
    // applied.
    let basename = auxencode(lowerencode(file), dotencode);
    let hex_sha = sha1.to_hex();

    let mut res = vec![];
    res.push(&b"dh/"[..]);
    res.push(&shortdirs);
    // filler is inserted after shortdirs but before sha. Let's remember the index.
    // This is part of the basename that is as long as possible given that the resulting string
    // is shorter that MAXSTOREPATHLEN.
    let filler_index = res.len();
    res.push(hex_sha.as_bytes());
    res.push(get_extension(&basename));

    let filler = {
        let current_len = res.iter().map(|elem| elem.len()).sum::<usize>();
        let spaceleft = MAXSTOREPATHLEN - current_len;
        let size = cmp::min(basename.len(), spaceleft);
        &basename[..size]
    };
    res.insert(filler_index, filler);
    PathBuf::from(String::from_utf8(res.concat()).expect("bad utf8"))
}

#[cfg(test)]
mod test {
    use super::*;

    fn check_fsencode(path: &[u8], expected: &str) {
        let mut elements = vec![];
        let path = &MPath::new(path).unwrap();
        elements.extend(path.into_iter().cloned());

        assert_eq!(fncache_fsencode(&elements, false), PathBuf::from(expected));
    }

    fn check_simple_fsencode(path: &[u8], expected: &str) {
        let mut elements = vec![];
        let path = &MPath::new(path).unwrap();
        elements.extend(path.into_iter().cloned());

        assert_eq!(simple_fsencode(&elements), PathBuf::from(expected));
    }

    #[test]
    fn fsencode_simple() {
        check_fsencode(b"foo/bar", "foo/bar");
    }

    #[test]
    fn fsencode_simple_single() {
        check_fsencode(b"bar", "bar");
    }

    #[test]
    fn fsencode_hexquote() {
        check_fsencode(b"oh?/wow~:<>", "oh~3f/wow~7e~3a~3c~3e");
    }

    #[test]
    fn fsencode_direncode() {
        check_fsencode(b"foo.d/bar.d", "foo.d.hg/bar.d");
        check_fsencode(b"foo.d/bar.d/file", "foo.d.hg/bar.d.hg/file");
        check_fsencode(b"tests/legacy-encoding.hg", "tests/legacy-encoding.hg");
        check_fsencode(
            b"tests/legacy-encoding.hg/file",
            "tests/legacy-encoding.hg.hg/file",
        );
    }

    #[test]
    fn fsencode_direncode_single() {
        check_fsencode(b"bar.d", "bar.d");
    }

    #[test]
    fn fsencode_upper() {
        check_fsencode(b"HELLO/WORLD", "_h_e_l_l_o/_w_o_r_l_d");
    }

    #[test]
    fn fsencode_upper_direncode() {
        check_fsencode(b"HELLO.d/WORLD.d", "_h_e_l_l_o.d.hg/_w_o_r_l_d.d");
    }

    #[test]
    fn fsencode_single_underscore_fileencode() {
        check_fsencode(b"_", "__");
    }

    #[test]
    fn fsencode_auxencode() {
        check_fsencode(b"com3", "co~6d3");
        check_fsencode(b"lpt9", "lp~749");
        check_fsencode(b"com", "com");
        check_fsencode(b"lpt.3", "lpt.3");
        check_fsencode(b"com3x", "com3x");
        check_fsencode(b"xcom3", "xcom3");
        check_fsencode(b"aux", "au~78");
        check_fsencode(b"auxx", "auxx");
        check_fsencode(b" ", "~20");
        check_fsencode(b"aux ", "aux~20");
    }

    fn join_and_check(prefix: Option<&str>, suffix: Option<&str>, expected: &str) {
        let prefix = prefix.map(|prefix| MPath::new(prefix).unwrap());
        let suffix = suffix.map(|suffix| MPath::new(suffix).unwrap());
        let mut elements = vec![];
        let joined = MPath::join_opt(prefix.as_ref(), MPath::iter_opt(suffix.as_ref()));
        elements.extend(MPath::vec_iter_opt(joined));
        assert_eq!(fncache_fsencode(&elements, false), PathBuf::from(expected));
    }

    #[test]
    fn join() {
        join_and_check(Some("prefix"), Some("suffix"), "prefix/suffix");
        join_and_check(Some("prefix"), None, "prefix");
        join_and_check(None, Some("suffix"), "suffix");

        assert_eq!(MPath::new(b"asdf").unwrap().join(None).to_vec().len(), 4);

        assert_eq!(
            MPath::new(b"asdf")
                .unwrap()
                .join(&MPathElement::new(b"bdc".to_vec()).expect("valid MPathElement"))
                .to_vec()
                .len(),
            8
        );
    }

    #[test]
    fn test_get_extension() {
        assert_eq!(get_extension(b".foo"), b"");
        assert_eq!(get_extension(b"foo."), b".");
        assert_eq!(get_extension(b"foo"), b"");
        assert_eq!(get_extension(b"foo.txt"), b".txt");
        assert_eq!(get_extension(b"foo.bar.blat"), b".blat");
    }

    #[test]
    fn test_hashed_file() {
        let dirs = vec![Vec::from(&b"asdf"[..]), Vec::from("asdf")];
        let file = b"file.txt";
        assert_eq!(
            hashed_file(&dirs, file),
            crate::types::NodeHash::from_slice(&b"asdf/asdf/file.txt"[..])
        );
    }

    #[test]
    fn test_fsencode() {
        let toencode = b"data/abcdefghijklmnopqrstuvwxyz0123456789 !#%&'()+,-.;=[]^`{}";
        let expected = "data/abcdefghijklmnopqrstuvwxyz0123456789 !#%&'()+,-.;=[]^`{}";
        check_fsencode(&toencode[..], expected);

        let toencode = b"data/\x02\x03\x04\x05\x06\x07\x08\t\x0b\x0c\r\x0e\x0f\x10\x11\x12\x13\x14\x15\x16\x17\x18\x19\x1a\x1b\x1c\x1d\x1e\x1f";
        let expected = "data/~02~03~04~05~06~07~08~09~0b~0c~0d~0e~0f~10~11~12~13~14~15~16~17~18~19~1a~1b~1c~1d~1e~1f";
        check_fsencode(&toencode[..], expected);
    }

    #[test]
    fn test_simple_fsencode() {
        let toencode: &[u8] = b"foo.i/bar.d/bla.hg/hi:world?/HELLO";
        let expected = "foo.i.hg/bar.d.hg/bla.hg.hg/hi~3aworld~3f/_h_e_l_l_o";

        check_simple_fsencode(toencode, expected);

        let toencode: &[u8] = b".arcconfig.i";
        let expected = ".arcconfig.i";
        check_simple_fsencode(toencode, expected);
    }

    /// Tested as in D8527475
    #[test]
    fn test_very_long_simple_fsencode() {
        let toencode = vec![b'X'; 128];
        let expected = "XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX";

        check_simple_fsencode(&toencode, expected);

        let toencode = vec![b'X'; 127];
        let expected = "_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x";

        check_simple_fsencode(&toencode, expected);

        let mut toencode = vec![b'Z', b'/'];
        toencode.append(&mut vec![b'X'; 128]);
        toencode.push(b'/');
        toencode.append(&mut vec![b'Y'; 127]);
        let expected = "_z/XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX/_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y_y";

        check_simple_fsencode(&toencode, expected);
    }

    // Tested as in D9967059
    #[test]
    fn test_hg() {
        let mut toencode = vec![b'X'; 253];
        toencode.push(b'_');
        let expected = "XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX__";
        check_simple_fsencode(&toencode, expected);

        let mut toencode = vec![b'X'; 254];
        toencode.push(b'_');
        let expected = "XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX:";
        check_simple_fsencode(&toencode, expected);

        let x = vec![vec![b'X', b'_']; 85];
        let mut x_flatten: Vec<u8> = x.iter().flat_map(|array| array.iter()).cloned().collect();
        let y = vec![vec![b'Y', b'_']; 86];
        let mut y_flatten: Vec<u8> = y.iter().flat_map(|array| array.iter()).cloned().collect();

        let mut toencode = vec![b'Z', b'/'];
        toencode.append(&mut x_flatten);
        toencode.push(b'/');
        toencode.append(&mut y_flatten);
        let expected = "_z/X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__X__/Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:Y:";
        check_simple_fsencode(&toencode, expected);

        let toencode: &[u8] = b"X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X";
        let expected = "X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X:X";
        check_simple_fsencode(toencode, expected);

        let toencode: &[u8] = b"A/Y__Y__Y__Y__Y__Y__Y__Y__Y__Y__Y__Y__Y__Y__Y__Y__Y__Y__Y__Y__Y__Y__Y__Y__Y__Y__Y__Y__Y__Y__Y__Y__Y__Y__Y__Y__Y__Y__Y__Y__Y__Y__Y__Y__Y__Y__Y__Y__Y__Y__Y__Y__Y__Y__Y__Y__Y__Y__Y__Y__Y__Y__Y__Y__Y__Y/ZZZ/XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX";
        let expected = "_a/Y::Y::Y::Y::Y::Y::Y::Y::Y::Y::Y::Y::Y::Y::Y::Y::Y::Y::Y::Y::Y::Y::Y::Y::Y::Y::Y::Y::Y::Y::Y::Y::Y::Y::Y::Y::Y::Y::Y::Y::Y::Y::Y::Y::Y::Y::Y::Y::Y::Y::Y::Y::Y::Y::Y::Y::Y::Y::Y::Y::Y::Y::Y::Y::Y::Y/_z_z_z/_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x_x";
        check_simple_fsencode(toencode, expected);
    }

}

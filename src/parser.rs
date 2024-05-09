use std::{io::Read as _, sync::Arc};

use flate2::read::ZlibDecoder;
use nom::{
    branch::alt,
    bytes::complete::{tag, take},
    combinator::{complete, peek},
    error::ErrorKind,
    multi::{length_data, many0},
    number::complete::{be_u16, be_u32},
    sequence::tuple,
    Err, IResult, Needed, Parser,
};

use super::types::{
    Delta, Features, Fragment, IdxFlags, NodeHash, RevisionLogEntry, RevisionLogHeader, Version,
};

/// Parse a 6 byte big-endian offset
#[inline]
fn be_u48(i: &[u8]) -> IResult<&[u8], u64> {
    if i.len() < 6 {
        Err(Err::Incomplete(Needed::new(6 - i.len())))
    } else {
        let res = (u64::from(i[0]) << 40)
            + (u64::from(i[1]) << 32)
            + (u64::from(i[2]) << 24)
            + (u64::from(i[3]) << 16)
            + (u64::from(i[4]) << 8)
            + u64::from(i[5]);
        Ok((&i[6..], res))
    }
}

/// Unpack data with zlib.
fn zlib_decompress(input: &[u8]) -> IResult<&[u8], Vec<u8>> {
    let mut data = Vec::new();

    let inused = {
        let mut zdec = ZlibDecoder::new(input);

        match zdec.read_to_end(&mut data) {
            Ok(_) => zdec.total_in() as usize,
            Err(_) => return Err(Err::Error(nom::error::Error::new(input, ErrorKind::Fail))),
        }
    };

    Ok((&input[inused..], data))
}

// Parse the revlog header
pub fn header(input: &[u8]) -> IResult<&[u8], RevisionLogHeader> {
    let (input, (features, version)) = be_u16.and(be_u16).parse(input)?;
    let Some(features) = Features::from_bits(features) else {
        return Err(Err::Error(nom::error::Error::new(input, ErrorKind::Fail)));
    };
    let version = match version {
        0 => Version::Revlog0,
        1 => Version::RevlogNG,
        _ => return Err(Err::Error(nom::error::Error::new(input, ErrorKind::Fail))),
    };
    Ok((input, RevisionLogHeader { version, features }))
}

pub const fn indexng_size() -> usize {
    6 + 2 + 4 + 4 + 4 + 4 + 4 + 4 + 32
}

// Parse an "NG" revlog entry
pub fn indexng(input: &[u8]) -> IResult<&[u8], RevisionLogEntry> {
    let (
        input,
        (offset, flags, compressed_length, uncompressed_length, baserev, linkrev, p1, p2, hash),
    ) = tuple((
        be_u48,
        be_u16,
        be_u32,
        be_u32,
        be_u32,
        be_u32,
        be_u32,
        be_u32,
        take(32usize),
    ))(input)?;
    Ok((
        input,
        RevisionLogEntry {
            offset,
            flags: IdxFlags::from_bits(flags).expect("bad rev idx flags"),
            compressed_len: compressed_length,
            len: Some(uncompressed_length),
            baserev: if baserev == !0 {
                None
            } else {
                Some(baserev.into())
            },
            linkrev: linkrev.into(),
            p1: if p1 == !0 { None } else { Some(p1.into()) },
            p2: if p2 == !0 { None } else { Some(p2.into()) },
            nodeid: NodeHash::from(&hash[..20]),
        },
    ))
}

pub const fn index0_size() -> usize {
    4 + 4 + 4 + 4 + 4 + 4 + 4 + 20
}

// Parse an original revlog entry
pub fn index0(input: &[u8]) -> IResult<&[u8], RevisionLogEntry> {
    let (input, (_header, offset, compressed_length, baserev, linkrev, p1, p2, hash)) =
        tuple((
            header,
            be_u32,
            be_u32,
            be_u32,
            be_u32,
            be_u32,
            be_u32,
            take(20usize),
        ))(input)?;
    Ok((
        input,
        RevisionLogEntry {
            offset: u64::from(offset),
            flags: IdxFlags::empty(),
            compressed_len: compressed_length,
            len: None,
            baserev: if baserev == !0 {
                None
            } else {
                Some(baserev.into())
            },
            linkrev: linkrev.into(),
            p1: if p1 == !0 { None } else { Some(p1.into()) },
            p2: if p2 == !0 { None } else { Some(p2.into()) },
            nodeid: NodeHash::from(&hash[..20]),
        },
    ))
}

// Parse a single Delta
fn delta(input: &[u8]) -> IResult<&[u8], Fragment> {
    tuple((be_u32, be_u32, length_data(be_u32)))
        .map(|(start, end, content): (_, _, &[u8])| Fragment {
            start: start as usize,
            end: end as usize,
            content: content.into(),
        })
        .parse(input)
}

// Parse 0 or more deltas
fn deltas(input: &[u8]) -> IResult<&[u8], Vec<Fragment>> {
    many0(delta)(input)
}

fn compressed_deltas(input: &[u8]) -> IResult<&[u8], Vec<Fragment>> {
    let (input, chunk) = zlib_decompress(input)?;

    let Ok((_remain, d)) = deltas(&chunk) else {
        return Err(Err::Error(nom::error::Error::new(input, ErrorKind::Fail)));
    };

    Ok((input, d))
}

// A chunk of data data that contains some Deltas; the caller defines the framing bytes
// bounding the input.
pub fn deltachunk(input: &[u8]) -> IResult<&[u8], Delta> {
    let (input, dv) = many0(
        complete(alt((
            tag(b"u").and(deltas),                  // uncompressed with explicit 'u' header
            peek(tag(b"\0")).and(deltas),           // uncompressed with included initial 0x00
            peek(tag(b"x")).and(compressed_deltas), // compressed; 'x' part of the zlib stream
        )))
        .map(|(_, d)| d),
    )(input)?;
    Ok((
        input,
        Delta {
            fragments: dv.into_iter().flatten().collect(),
        },
    ))
}

fn remains(input: &[u8]) -> IResult<&[u8], Arc<[u8]>> {
    Ok((&input[..0], input.into()))
}

fn compressed_remains(input: &[u8]) -> IResult<&[u8], Arc<[u8]>> {
    let (input, chunk) = zlib_decompress(input)?;

    let Ok((_remain, d)) = remains(&chunk) else {
        return Err(Err::Error(nom::error::Error::new(input, ErrorKind::Fail)));
    };

    Ok((input, d))
}

// Parse some literal data, possibly compressed
pub fn literal(input: &[u8]) -> IResult<&[u8], Arc<[u8]>> {
    let (input, (_, d)) = alt((
        // uncompressed with explicit 'u' header
        tag(b"u").and(remains),
        // uncompressed with included initial 0x00
        peek(tag(b"\0")).and(remains),
        // compressed; 'x' part of the zlib stream
        peek(tag(b"x")).and(compressed_remains),
    ))(input)?;
    Ok((input, d))
}

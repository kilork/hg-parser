use flate2::read::ZlibDecoder;
use nom::{
    alt, alt_complete, apply, be_u16, be_u32, complete, do_parse, length_bytes, many0, map, named,
    peek, return_error, tag, take, Context, Err, ErrorKind, IResult, Needed,
};
use std::fmt::Debug;
use std::io::Read;

use super::types::*;

pub mod badness {
    use super::Error;
    pub const IO: Error = 0;
}

pub type Error = u32;

/// Parse a 6 byte big-endian offset
#[inline]
fn be_u48(i: &[u8]) -> IResult<&[u8], u64> {
    if i.len() < 6 {
        Err(Err::Incomplete(Needed::Size(6 - i.len())))
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

/// Unpack a chunk of data and apply a parse function to the output.
fn zlib_decompress<'a, P, R: 'a, E: Debug + 'a>(i: &'a [u8], parse: P) -> IResult<&'a [u8], R, E>
where
    for<'p> P: Fn(&'p [u8]) -> IResult<&'p [u8], R, E>,
{
    let mut data = Vec::new();

    let inused = {
        let mut zdec = ZlibDecoder::new(i);

        match zdec.read_to_end(&mut data) {
            Ok(_) => zdec.total_in() as usize,
            Err(err) => panic!("zdec failed {:?}", err),
        }
    };

    let remains = &i[inused..];

    detach_result(parse(&data[..]), remains)
}

// Parse the revlog header
named!(pub header<RevisionLogHeader>,
    do_parse!(
        features: return_error!(ErrorKind::Custom(badness::IO), be_u16) >>
        version: return_error!(ErrorKind::Custom(badness::IO), be_u16) >>
        ({
            let vers = match version {
                0 => Version::Revlog0,
                1 => Version::RevlogNG,
                _ => panic!("bad version"),
            };

            let features = match Features::from_bits(features) {
                Some(f) => f,
                None => panic!("bad features"),
            };

            RevisionLogHeader {
                version: vers,
                features: features,
            }
        }))
);

pub const fn indexng_size() -> usize {
    6 + 2 + 4 + 4 + 4 + 4 + 4 + 4 + 32
}

// Parse an "NG" revlog entry
named!(pub indexng<RevisionLogEntry>,
    do_parse!(
        offset: return_error!(ErrorKind::Custom(badness::IO), be_u48) >>    // XXX if first, then only 2 bytes, implied 0 in top 4
        flags: return_error!(ErrorKind::Custom(badness::IO), be_u16) >>     // ?
        compressed_length: return_error!(ErrorKind::Custom(badness::IO), be_u32) >>
        uncompressed_length: return_error!(ErrorKind::Custom(badness::IO), be_u32) >>
        baserev: return_error!(ErrorKind::Custom(badness::IO), be_u32) >>
        linkrev: return_error!(ErrorKind::Custom(badness::IO), be_u32) >>
        p1: return_error!(ErrorKind::Custom(badness::IO), be_u32) >>
        p2: return_error!(ErrorKind::Custom(badness::IO), be_u32) >>
        hash: take!(32) >>
        ({
            RevisionLogEntry {
                offset: offset,
                flags: IdxFlags::from_bits(flags).expect("bad rev idx flags"),
                compressed_len: compressed_length,
                len: Some(uncompressed_length),
                baserev: if baserev == !0 { None } else { Some(baserev.into()) },
                linkrev: linkrev.into(),
                p1: if p1 == !0 { None } else { Some(p1.into()) },
                p2: if p2 == !0 { None } else { Some(p2.into()) },
                nodeid: NodeHash::from(&hash[..20]),
            }
        })
    )
);

pub const fn index0_size() -> usize {
    4 + 4 + 4 + 4 + 4 + 4 + 4 + 20
}

// Parse an original revlog entry
named!(pub index0<RevisionLogEntry>,
    do_parse!(
        _header: header >>
        offset: return_error!(ErrorKind::Custom(badness::IO), be_u32) >>
        compressed_length: return_error!(ErrorKind::Custom(badness::IO), be_u32) >>
        baserev: return_error!(ErrorKind::Custom(badness::IO), be_u32) >>
        linkrev: return_error!(ErrorKind::Custom(badness::IO), be_u32) >>
        p1: return_error!(ErrorKind::Custom(badness::IO), be_u32) >>
        p2: return_error!(ErrorKind::Custom(badness::IO), be_u32) >>
        hash: take!(20) >>
        ({
            RevisionLogEntry {
                offset: u64::from(offset),
                flags: IdxFlags::empty(),
                compressed_len: compressed_length,
                len: None,
                baserev: if baserev == !0 { None } else { Some(baserev.into()) },
                linkrev: linkrev.into(),
                p1: if p1 == !0 { None } else { Some(p1.into()) },
                p2: if p2 == !0 { None } else { Some(p2.into()) },
                nodeid: NodeHash::from(&hash[..20]),
            }
        })
    )
);

// Parse a single Delta
named!(pub delta<Fragment>,
    do_parse!(
        start: be_u32 >>
        end: be_u32 >>
        content: length_bytes!(be_u32) >>
        ({
            Fragment {
                start: start as usize,
                end: end as usize,
                content: content.into(),
            }
        })
    )
);

// Parse 0 or more deltas
named!(deltas<Vec<Fragment>>, many0!(complete!(delta)));

// A chunk of data data that contains some Deltas; the caller defines the framing bytes
// bounding the input.
named!(pub deltachunk<Delta>,
    map!(
        many0!(
            alt_complete!(
                do_parse!(tag!(b"u") >> d: deltas >> (d)) |                                  // uncompressed with explicit 'u' header
                do_parse!(peek!(tag!(b"\0")) >> d: deltas >> (d)) |                          // uncompressed with included initial 0x00
                do_parse!(peek!(tag!(b"x")) >> d: apply!(zlib_decompress, deltas) >> (d))    // compressed; 'x' part of the zlib stream
            )
        ),
        |dv: Vec<_>| Delta { fragments: dv.into_iter().flat_map(|x| x).collect() }
    )
);

fn remains(i: &[u8]) -> IResult<&[u8], &[u8]> {
    Ok((&i[..0], i))
}

// Remap error to remove reference to `data`
pub fn detach_result<'inp, 'out, O: 'out, E: 'out>(
    res: IResult<&'inp [u8], O, E>,
    rest: &'out [u8],
) -> IResult<&'out [u8], O, E> {
    match res {
        Ok((_, o)) => Ok((rest, o)),
        Err(Err::Incomplete(n)) => Err(Err::Incomplete(n)),
        Err(Err::Error(Context::Code(_, e))) => Err(Err::Error(Context::Code(&b""[..], e))),
        Err(Err::Failure(Context::Code(_, e))) => Err(Err::Failure(Context::Code(&b""[..], e))),
    }
}

named!(remains_owned<Vec<u8>>, map!(remains, |x: &[u8]| x.into()));

// Parse some literal data, possibly compressed
named!(pub literal<Vec<u8>>,
    alt!(
        do_parse!(peek!(tag!(b"\0")) >> d: remains >> (d.into())) |
        do_parse!(peek!(tag!(b"x")) >> d: apply!(zlib_decompress, remains_owned) >> (d)) |
        do_parse!(tag!(b"u") >> d: remains >> (d.into()))
    )
);

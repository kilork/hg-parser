#[derive(Debug)]
pub enum ErrorKind {
    /// Parser failed.
    Parser,
    /// Cannot convert from Utf-8.
    FromUtf8(std::str::Utf8Error),
    /// IO error.
    IO(std::io::Error),
    /// Invalid path.
    InvalidPath(String),
    /// RevisionLog load failure.
    RevisionLogFailure(String),
    /// Cannot convert date/time.
    InvalidDateTime(String),
    /// Requirement in ``.hg/requires`` is not supported.
    UnknownRequirement(String),
    /// Manifest issue.
    Manifest(String),
}

impl From<std::io::Error> for ErrorKind {
    fn from(value: std::io::Error) -> Self {
        ErrorKind::IO(value)
    }
}

impl From<nom::Err<&[u8]>> for ErrorKind {
    fn from(_value: nom::Err<&[u8]>) -> Self {
        ErrorKind::Parser
    }
}

impl From<chrono::format::ParseError> for ErrorKind {
    fn from(value: chrono::format::ParseError) -> Self {
        ErrorKind::InvalidDateTime(format!("{:?}", value))
    }
}

impl From<std::str::Utf8Error> for ErrorKind {
    fn from(value: std::str::Utf8Error) -> Self {
        ErrorKind::FromUtf8(value)
    }
}

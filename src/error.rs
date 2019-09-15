use failure::Fail;

#[derive(Debug, Fail)]
pub enum ErrorKind {
    /// Parser failed.
    #[fail(display = "parser failed")]
    Parser,
    /// Cannot convert from Utf-8.
    #[fail(display = "cannot convert from Utf-8 {}", _0)]
    FromUtf8(std::str::Utf8Error),
    /// IO error.
    #[fail(display = "IO error {}", _0)]
    IO(std::io::Error),
    /// Invalid path.
    #[fail(display = "Invalid path {}", _0)]
    InvalidPath(String),
    /// RevisionLog load failure.
    #[fail(display = "revision log load failure {}", _0)]
    RevisionLogFailure(String),
    /// Cannot convert date/time.
    #[fail(display = "invalid date time {}", _0)]
    InvalidDateTime(String),
    /// Requirement in ``.hg/requires`` is not supported.
    #[fail(display = "unknown requirement {}", _0)]
    UnknownRequirement(String),
    /// Manifest issue.
    #[fail(display = "manifest issue {}", _0)]
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

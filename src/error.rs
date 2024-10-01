use crate::types::RepositoryRequire;

#[derive(Debug, thiserror::Error)]
pub enum ErrorKind {
    /// Parser failed.
    #[error("parser failed")]
    Parser,
    /// Cannot convert from Utf-8.
    #[error("cannot convert from Utf-8 {0}")]
    FromUtf8(#[from] std::str::Utf8Error),
    /// IO error.
    #[error("IO error {0}")]
    IO(#[from] std::io::Error),
    /// Invalid path.
    #[error("Invalid path {0}")]
    InvalidPath(String),
    /// RevisionLog load failure.
    #[error("revision log load failure {0}")]
    RevisionLogFailure(String),
    /// Cannot convert date/time.
    #[error("invalid date time {0}")]
    InvalidDateTime(String),
    /// Requirement in ``.hg/requires`` is not supported.
    #[error("unknown requirement {0}")]
    UnknownRequirement(RepositoryRequire),
    /// Manifest issue.
    #[error("manifest issue {0}")]
    Manifest(String),
}

impl From<nom::Err<nom::error::Error<&[u8]>>> for ErrorKind {
    fn from(_value: nom::Err<nom::error::Error<&[u8]>>) -> Self {
        ErrorKind::Parser
    }
}

impl From<chrono::format::ParseError> for ErrorKind {
    fn from(value: chrono::format::ParseError) -> Self {
        ErrorKind::InvalidDateTime(format!("{:?}", value))
    }
}

//! Error types for TRON operations.

use std::fmt;

/// Error type for TRON operations.
#[derive(Debug, Clone, PartialEq)]
pub enum Error {
    // Document errors
    /// Document does not end with "TRON" magic bytes.
    InvalidMagic,
    /// Document is too small to contain a valid footer.
    DocumentTooSmall,

    // Tag/type errors
    /// Invalid tag type bits (must be 0-7).
    InvalidTagType(u8),
    /// Expected one type but found another.
    UnexpectedType {
        expected: &'static str,
        found: &'static str,
    },

    // Address errors
    /// Address is beyond the document bounds.
    AddressOutOfBounds { addr: u32, len: usize },

    // Value parsing errors
    /// Text value contains invalid UTF-8.
    InvalidUtf8,
    /// Invalid length encoding in txt/bin value.
    InvalidLengthEncoding,
    /// Value data is truncated (not enough bytes).
    TruncatedValue,

    // Trie errors
    /// Key not found in map.
    KeyNotFound,
    /// Array index out of bounds.
    IndexOutOfBounds { index: u32, length: u32 },
    /// HAMT traversal exceeded maximum depth (7).
    MaxDepthExceeded,

    // JSON errors
    /// Failed to parse JSON input.
    JsonParse(String),
    /// Failed to serialize to JSON.
    JsonSerialize(String),
    /// f64 is NaN or Infinity (not representable in JSON).
    NonFiniteFloat(f64),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::InvalidMagic => write!(f, "invalid magic: expected TRON"),
            Error::DocumentTooSmall => write!(f, "document too small for footer"),
            Error::InvalidTagType(t) => write!(f, "invalid tag type: {t}"),
            Error::UnexpectedType { expected, found } => {
                write!(f, "expected {expected}, found {found}")
            }
            Error::AddressOutOfBounds { addr, len } => {
                write!(f, "address {addr:#x} out of bounds (len={len})")
            }
            Error::InvalidUtf8 => write!(f, "invalid UTF-8 in text value"),
            Error::InvalidLengthEncoding => write!(f, "invalid length encoding"),
            Error::TruncatedValue => write!(f, "truncated value data"),
            Error::KeyNotFound => write!(f, "key not found"),
            Error::IndexOutOfBounds { index, length } => {
                write!(f, "index {index} out of bounds (length={length})")
            }
            Error::MaxDepthExceeded => write!(f, "max HAMT depth exceeded"),
            Error::JsonParse(msg) => write!(f, "JSON parse error: {msg}"),
            Error::JsonSerialize(msg) => write!(f, "JSON serialize error: {msg}"),
            Error::NonFiniteFloat(n) => write!(f, "cannot encode non-finite float {n} as JSON"),
        }
    }
}

impl std::error::Error for Error {}

/// Result type alias for TRON operations.
pub type Result<T> = std::result::Result<T, Error>;

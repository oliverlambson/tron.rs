//! TRON (TRie Object Notation) - A binary format for JSON-compatible data.
//!
//! TRON uses HAMT (Hash Array Mapped Trie) for maps and vector tries for arrays,
//! enabling fast copy-on-write updates without rewriting the entire document.
//!
//! # Architecture
//!
//! This library uses a zero-copy architecture where bytes are the source of truth:
//!
//! - **Zero-copy reads**: Values are read directly from the underlying bytes
//! - **Copy-on-write mutations**: Modifications append new nodes, old data is preserved
//! - **Lazy evaluation**: Values are decoded on-demand via accessor methods
//!
//! # Example
//!
//! ```
//! use tron::{Document, Typed, map, encode::MapLeaf};
//!
//! // Open an existing document
//! let data = &[
//!     0x00, // nil value
//!     0x00, 0x00, 0x00, 0x00, // root_addr = 0
//!     0x00, 0x00, 0x00, 0x00, // prev_root_addr = 0
//!     b'T', b'R', b'O', b'N', // magic
//! ];
//! let doc = Document::from_slice(data).unwrap();
//! assert!(matches!(doc.root().typed(), Typed::Nil));
//!
//! // Create a new document with an empty map
//! let mut doc = Document::from_value(MapLeaf(&[]));
//!
//! // Add a value
//! let val_addr = doc.append(42i64);
//! let root = doc.root_addr();
//! let new_root = map::map_set(&mut doc, root, "answer", val_addr).unwrap();
//! doc.set_root(new_root);
//!
//! // Read it back
//! let val_addr = map::map_get(doc.as_bytes(), doc.root_addr(), "answer").unwrap();
//! assert!(val_addr.is_some());
//! ```

pub mod arr;
pub mod document;
pub mod encode;
pub mod error;
pub mod map;
pub mod tag;
pub mod value;
mod xxh32;

// Re-exports for convenience
pub use document::Document;
pub use error::{Error, Result};
pub use value::{ArrNode, MapNode, Typed, Value};

// Re-export xxh32 for users who need direct access to the hash function
pub use xxh32::xxh32;

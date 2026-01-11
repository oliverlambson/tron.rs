//! TRON document wrapper with copy-on-write semantics.
//!
//! A TRON document has a 4-byte header and an 8-byte footer:
//! - Header (4 bytes): Magic "TRON"
//! - Footer (8 bytes): Root address (u32 LE) + Previous root address (u32 LE)

use std::borrow::Cow;

use crate::encode::Encode;
use crate::error::{Error, Result};
use crate::value::Value;

/// Header size in bytes (magic "TRON").
const HEADER_SIZE: usize = 4;

/// Footer size in bytes (`root_addr` + `prev_root_addr`).
const FOOTER_SIZE: usize = 8;

/// Minimum document size: 4-byte header + 1-byte nil value + 8-byte footer.
const MIN_DOCUMENT_SIZE: usize = 13;

/// Magic bytes at the start of every TRON document.
const MAGIC: &[u8; 4] = b"TRON";

/// A TRON document with zero-copy reading and copy-on-write mutations.
///
/// When opened from a borrowed slice, reads are zero-copy. The first mutation
/// triggers allocation via `Cow::to_mut()`, after which subsequent mutations
/// reuse the owned buffer.
pub struct Document<'a> {
    /// The document buffer - borrowed for reads, owned (Vec) for mutations.
    data: Cow<'a, [u8]>,
    /// Cached root address (from footer).
    root_addr: u32,
    /// Cached previous root address (from footer).
    prev_root_addr: u32,
}

impl<'a> Document<'a> {
    /// Open an existing TRON document from a byte slice (zero-copy).
    ///
    /// Validates the magic bytes, footer, and that the root address points to
    /// a valid value.
    ///
    /// # Errors
    ///
    /// Returns `Error::DocumentTooSmall` if the data is less than 13 bytes.
    /// Returns `Error::InvalidMagic` if the magic bytes are not "TRON".
    /// Returns `Error::AddressOutOfBounds` if the root address is invalid.
    pub fn from_slice(data: &'a [u8]) -> Result<Self> {
        if data.len() < MIN_DOCUMENT_SIZE {
            return Err(Error::DocumentTooSmall);
        }

        // Verify magic in header (first 4 bytes)
        if &data[..HEADER_SIZE] != MAGIC {
            return Err(Error::InvalidMagic);
        }

        // Parse footer (last 8 bytes)
        let footer_start = data.len() - FOOTER_SIZE;

        let root_addr = u32::from_le_bytes([
            data[footer_start],
            data[footer_start + 1],
            data[footer_start + 2],
            data[footer_start + 3],
        ]);

        let prev_root_addr = u32::from_le_bytes([
            data[footer_start + 4],
            data[footer_start + 5],
            data[footer_start + 6],
            data[footer_start + 7],
        ]);

        // Validate that root_addr points to a readable value
        Value::new(data, root_addr)?;

        Ok(Self {
            data: Cow::Borrowed(data),
            root_addr,
            prev_root_addr,
        })
    }

    /// Create a new document from an encodable value.
    ///
    /// The value must implement the [`Encode`] trait. This includes primitive
    /// types like `bool`, `i64`, `f64`, `&str`, as well as container types
    /// like [`MapLeaf`](crate::encode::MapLeaf) and [`ArrLeaf`](crate::encode::ArrLeaf).
    ///
    /// # Example
    ///
    /// ```
    /// use tron::{Document, TypedValue, encode::{Nil, MapLeaf}};
    ///
    /// // Create document with nil root
    /// let doc = Document::from_value(&Nil);
    /// assert!(matches!(doc.root().typed(), Ok(TypedValue::Nil)));
    ///
    /// // Create document with i64 root
    /// let doc = Document::from_value(&42i64);
    /// assert!(matches!(doc.root().typed(), Ok(TypedValue::I64(42))));
    ///
    /// // Create document with string root
    /// let doc = Document::from_value(&"hello");
    /// assert!(matches!(doc.root().typed(), Ok(TypedValue::Str("hello"))));
    ///
    /// // Create document with empty map root
    /// let doc = Document::from_value(&MapLeaf(&[]));
    /// assert!(matches!(doc.root().typed(), Ok(TypedValue::Map(_))));
    /// ```
    #[must_use]
    pub fn from_value(value: &impl Encode) -> Document<'static> {
        Self::from_bytes(&value.encode())
    }

    /// Create a new document from raw encoded bytes.
    ///
    /// This is an internal method for use by tests and other modules.
    pub(crate) fn from_bytes(value_bytes: &[u8]) -> Document<'static> {
        let root_addr = HEADER_SIZE as u32; // Value starts after header
        let mut data = Vec::with_capacity(HEADER_SIZE + value_bytes.len() + FOOTER_SIZE);
        data.extend_from_slice(MAGIC); // Header: magic at start
        data.extend_from_slice(value_bytes); // Value bytes
        data.extend_from_slice(&root_addr.to_le_bytes()); // Footer: root_addr
        data.extend_from_slice(&[0, 0, 0, 0]); // Footer: prev_root_addr = 0

        Document {
            data: Cow::Owned(data),
            root_addr,
            prev_root_addr: 0,
        }
    }

    // --- Reading (zero-copy) ---

    /// Get the root value.
    ///
    /// # Panics
    ///
    /// Panics if the root address is invalid. This cannot happen for documents
    /// created via `from_slice` (which validates the root address) or `from_value`
    /// (which constructs a valid address).
    #[must_use]
    pub fn root(&self) -> Value<'_> {
        // SAFETY: root_addr is validated in from_slice, and from_value/from_bytes
        // always produce valid addresses
        Value::new(self.data.as_ref(), self.root_addr).expect("root_addr validated on construction")
    }

    /// Get a value at a specific address.
    ///
    /// # Errors
    ///
    /// Returns `Error::AddressOutOfBounds` if the address is outside the document.
    pub fn value_at(&self, addr: u32) -> Result<Value<'_>> {
        Value::new(self.data.as_ref(), addr)
    }

    /// Get the raw document bytes.
    #[inline]
    #[must_use]
    pub fn as_bytes(&self) -> &[u8] {
        self.data.as_ref()
    }

    /// Get the current root address.
    #[inline]
    #[must_use]
    pub fn root_addr(&self) -> u32 {
        self.root_addr
    }

    /// Get the previous root address.
    #[inline]
    #[must_use]
    pub fn prev_root_addr(&self) -> u32 {
        self.prev_root_addr
    }

    /// Get the document length in bytes.
    #[inline]
    #[must_use]
    pub fn len(&self) -> usize {
        self.data.len()
    }

    /// Check if the document is empty (should never be true for valid documents).
    #[inline]
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    // --- Writing (copy-on-write) ---

    /// Append an encoded value to the document and return its address.
    ///
    /// This triggers allocation on first mutation if the document was opened
    /// from a borrowed slice.
    ///
    /// The value is appended after the current footer. The old footer remains
    /// in place to preserve the history chain for traversal.
    ///
    /// # Example
    ///
    /// ```
    /// use tron::{Document, TypedValue, encode::MapLeaf};
    ///
    /// let mut doc = Document::from_value(&MapLeaf(&[]));
    /// let addr = doc.append(&42i64);
    /// assert!(matches!(doc.value_at(addr).unwrap().typed(), Ok(TypedValue::I64(42))));
    /// ```
    pub fn append(&mut self, value: &impl Encode) -> u32 {
        self.append_bytes(&value.encode())
    }

    /// Append raw bytes to the document and return the start address.
    ///
    /// This is an internal method for use by arr.rs and map.rs which
    /// generate encoded bytes dynamically.
    pub(crate) fn append_bytes(&mut self, bytes: &[u8]) -> u32 {
        // Get mutable access (allocates if currently borrowed)
        let vec = self.data.to_mut();

        // Append after current content
        let addr = vec.len() as u32;
        vec.extend_from_slice(bytes);

        addr
    }

    /// Update the root address and append a new footer.
    ///
    /// This appends a new footer with the new root address. The old footer
    /// remains in place, creating a linked list for history traversal.
    /// The `prev_root_addr` in the new footer points to the previous root.
    pub fn set_root(&mut self, new_root_addr: u32) {
        let old_root = self.root_addr;
        self.root_addr = new_root_addr;
        self.prev_root_addr = old_root;

        let vec = self.data.to_mut();

        // Append NEW footer (preserving old footer for history)
        vec.extend_from_slice(&self.root_addr.to_le_bytes());
        vec.extend_from_slice(&self.prev_root_addr.to_le_bytes());
    }

    /// Check if the document has been modified (owns its data).
    #[inline]
    #[must_use]
    pub fn is_modified(&self) -> bool {
        matches!(self.data, Cow::Owned(_))
    }

    /// Convert to an owned document with `'static` lifetime.
    ///
    /// This allocates if the document was opened from a borrowed slice.
    #[must_use]
    pub fn into_owned(self) -> Document<'static> {
        Document {
            data: Cow::Owned(self.data.into_owned()),
            root_addr: self.root_addr,
            prev_root_addr: self.prev_root_addr,
        }
    }

    /// Clone the document into an owned copy.
    #[must_use]
    pub fn to_owned(&self) -> Document<'static> {
        Document {
            data: Cow::Owned(self.data.as_ref().to_vec()),
            root_addr: self.root_addr,
            prev_root_addr: self.prev_root_addr,
        }
    }
}

impl std::fmt::Debug for Document<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Document")
            .field("len", &self.data.len())
            .field("root_addr", &format_args!("{:#x}", self.root_addr))
            .field(
                "prev_root_addr",
                &format_args!("{:#x}", self.prev_root_addr),
            )
            .field("is_modified", &self.is_modified())
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::encode;
    use crate::value::TypedValue;

    #[test]
    fn test_from_value_nil() {
        let doc = Document::from_value(&encode::encode_nil());
        assert_eq!(doc.len(), MIN_DOCUMENT_SIZE);
        assert_eq!(doc.root_addr(), HEADER_SIZE as u32); // Root is at offset 4
        assert!(matches!(doc.root().typed(), Ok(TypedValue::Nil)));
    }

    #[test]
    fn test_from_value_i64() {
        let doc = Document::from_value(&encode::encode_i64(42));
        assert!(matches!(doc.root().typed(), Ok(TypedValue::I64(42))));
    }

    #[test]
    fn test_from_value_empty_map() {
        use crate::value::MapNode;
        let doc = Document::from_bytes(&encode::encode_map_leaf(&[]));
        match doc.root().typed().unwrap() {
            TypedValue::Map(MapNode::Leaf(leaf)) => {
                assert_eq!(leaf.entry_count(), 0);
            }
            _ => panic!("expected Map leaf"),
        }
    }

    #[test]
    fn test_from_value_empty_arr() {
        let doc = Document::from_bytes(&encode::encode_arr_leaf(true, 0, 0, Some(0), &[]));
        match doc.root().typed().unwrap() {
            TypedValue::Arr(arr) => {
                assert!(arr.is_root());
                assert!(arr.is_leaf());
                assert_eq!(arr.length(), Some(0));
            }
            _ => panic!("expected Arr"),
        }
    }

    #[test]
    fn test_open_nil() {
        // Minimal nil document
        let data = [
            b'T', b'R', b'O', b'N', // magic (header)
            0x00, // nil @4
            0x04, 0x00, 0x00, 0x00, // root_addr = 4
            0x00, 0x00, 0x00, 0x00, // prev_root_addr = 0
        ];
        let doc = Document::from_slice(&data).unwrap();
        assert!(!doc.is_modified());
        assert!(matches!(doc.root().typed(), Ok(TypedValue::Nil)));
    }

    #[test]
    fn test_invalid_magic() {
        // Wrong magic at the start
        let data = [
            b'N', b'O', b'P', b'E', // wrong magic (header)
            0x00, // nil
            0x04, 0x00, 0x00, 0x00, // root_addr
            0x00, 0x00, 0x00, 0x00, // prev_root_addr
        ];
        assert!(matches!(
            Document::from_slice(&data),
            Err(Error::InvalidMagic)
        ));
    }

    #[test]
    fn test_too_small() {
        let data = [0x00, 0x00, 0x00];
        assert!(matches!(
            Document::from_slice(&data),
            Err(Error::DocumentTooSmall)
        ));
    }

    #[test]
    fn test_append_and_set_root() {
        // Start with nil document
        let data = [
            b'T', b'R', b'O', b'N', // magic (header)
            0x00, // nil @4
            0x04, 0x00, 0x00, 0x00, // root_addr = 4
            0x00, 0x00, 0x00, 0x00, // prev_root_addr = 0
        ];
        let mut doc = Document::from_slice(&data).unwrap();
        assert!(!doc.is_modified());

        // Append i64(42) - goes after the original footer
        let i64_bytes = [0x02, 0x2A, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00];
        let new_addr = doc.append(&i64_bytes);
        assert!(doc.is_modified());
        assert_eq!(new_addr, 13); // After header (4) + nil (1) + footer (8)

        // Update root - appends new footer
        doc.set_root(new_addr);
        assert_eq!(doc.root_addr(), 13);
        assert_eq!(doc.prev_root_addr(), 4); // Original root was @4

        // Verify new root
        let root = doc.root();
        assert!(matches!(root.typed(), Ok(TypedValue::I64(42))));

        // Verify document structure: old footer preserved, new footer at end
        // [header(4)][nil(1)][old_footer(8)][i64(9)][new_footer(8)] = 30 bytes
        assert_eq!(doc.len(), 30);
    }

    #[test]
    fn test_into_owned() {
        let data = [
            b'T', b'R', b'O', b'N', // magic (header)
            0x00, // nil @4
            0x04, 0x00, 0x00, 0x00, // root_addr = 4
            0x00, 0x00, 0x00, 0x00, // prev_root_addr = 0
        ];
        let doc = Document::from_slice(&data).unwrap();
        assert!(!doc.is_modified());

        let owned = doc.into_owned();
        assert!(owned.is_modified()); // Now owned
        assert!(matches!(owned.root().typed(), Ok(TypedValue::Nil)));
    }

    #[test]
    fn test_append_preserves_history() {
        // Test that append-only writes preserve the old footer for history traversal.
        //
        // Structure (new format with header at start):
        // Before: [header][data][footer1]
        // After:  [header][data][footer1][new_data][footer2]
        //
        // footer2.prev_root_addr should point to the old root, and
        // footer1 should still be readable at its original location.

        // Start with nil document
        let data = [
            b'T', b'R', b'O', b'N', // magic (header)
            0x00, // nil at @4
            0x04, 0x00, 0x00, 0x00, // root_addr = 4
            0x00, 0x00, 0x00, 0x00, // prev_root_addr = 0
        ];
        let mut doc = Document::from_slice(&data).unwrap();
        let original_len = doc.len(); // 13 bytes

        // First mutation: append i64(42) and update root
        let i64_bytes = [0x02, 0x2A, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00];
        let addr1 = doc.append(&i64_bytes);
        assert_eq!(addr1, 13); // After original document
        doc.set_root(addr1);

        // Verify structure after first mutation:
        // [header(4)][nil(1)][footer1(8)][i64(9)][footer2(8)] = 30 bytes
        assert_eq!(doc.len(), 30);
        assert_eq!(doc.root_addr(), 13);
        assert_eq!(doc.prev_root_addr(), 4); // Original root was @4

        // Verify the OLD footer is still present at its original location
        let old_footer_start = original_len - FOOTER_SIZE; // byte 5
        let old_footer = &doc.as_bytes()[old_footer_start..old_footer_start + FOOTER_SIZE];
        let old_root = u32::from_le_bytes(old_footer[0..4].try_into().unwrap());
        assert_eq!(old_root, 4); // Original root was nil @4

        // Second mutation: append i64(99) and update root again
        let i64_bytes2 = [0x02, 0x63, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00];
        let addr2 = doc.append(&i64_bytes2);
        assert_eq!(addr2, 30); // After footer2
        doc.set_root(addr2);

        // Verify structure after second mutation:
        // [header(4)][nil(1)][footer1(8)][i64(9)][footer2(8)][i64(9)][footer3(8)] = 47 bytes
        assert_eq!(doc.len(), 47);
        assert_eq!(doc.root_addr(), 30);
        assert_eq!(doc.prev_root_addr(), 13); // Previous root was @13

        // Verify we can still read footer1 at its original location
        let footer1 = &doc.as_bytes()[old_footer_start..old_footer_start + FOOTER_SIZE];
        let footer1_root = u32::from_le_bytes(footer1[0..4].try_into().unwrap());
        assert_eq!(footer1_root, 4); // Original root was @4

        // Verify we can still read footer2 (now in the middle)
        let footer2_start = 30 - FOOTER_SIZE; // 22
        let footer2 = &doc.as_bytes()[footer2_start..footer2_start + FOOTER_SIZE];
        let footer2_root = u32::from_le_bytes(footer2[0..4].try_into().unwrap());
        let footer2_prev = u32::from_le_bytes(footer2[4..8].try_into().unwrap());
        assert_eq!(footer2_root, 13); // Was pointing to i64(42)
        assert_eq!(footer2_prev, 4); // Its prev was nil @4

        // Verify the current (latest) footer at the end
        let footer3_start = doc.len() - FOOTER_SIZE;
        let footer3 = &doc.as_bytes()[footer3_start..];
        let footer3_root = u32::from_le_bytes(footer3[0..4].try_into().unwrap());
        let footer3_prev = u32::from_le_bytes(footer3[4..8].try_into().unwrap());
        assert_eq!(footer3_root, 30); // Points to i64(99)
        assert_eq!(footer3_prev, 13); // Previous root was i64(42)

        // Verify we can read all values
        let val1 = doc.value_at(4).unwrap(); // nil at @4
        assert!(matches!(val1.typed(), Ok(TypedValue::Nil)));

        let val2 = doc.value_at(13).unwrap();
        assert!(matches!(val2.typed(), Ok(TypedValue::I64(42))));

        let val3 = doc.value_at(30).unwrap();
        assert!(matches!(val3.typed(), Ok(TypedValue::I64(99))));

        // Current root should be i64(99)
        assert!(matches!(doc.root().typed(), Ok(TypedValue::I64(99))));
    }
}

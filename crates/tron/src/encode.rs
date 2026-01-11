//! Encoding utilities for writing TRON values.
//!
//! These functions serialize Rust values into TRON binary format.
//!
//! # The `Encode` Trait
//!
//! The [`Encode`] trait provides a type-safe way to encode values. It is
//! implemented for primitive Rust types that map directly to TRON types:
//!
//! | Rust Type | TRON Type |
//! |-----------|-----------|
//! | `Nil`     | nil       |
//! | `bool`    | bit       |
//! | `i64`     | i64       |
//! | `f64`     | f64       |
//! | `&str`    | txt       |
//! | `Bin`     | bin       |
//!
//! For container types (maps and arrays), use the dedicated structs:
//! [`MapLeaf`], [`MapBranch`], [`ArrLeaf`], [`ArrBranch`].

use crate::tag::{Tag, minimal_node_len_encoding, minimal_uint_encoding};

/// Trait for types that can be encoded as TRON values.
pub trait Encode {
    /// Encode this value as TRON bytes.
    fn encode(&self) -> Vec<u8>;
}

/// Nil value (JSON null).
#[derive(Debug, Clone, Copy, Default)]
pub struct Nil;

impl Encode for Nil {
    fn encode(&self) -> Vec<u8> {
        encode_nil().to_vec()
    }
}

impl Encode for bool {
    fn encode(&self) -> Vec<u8> {
        encode_bool(*self).to_vec()
    }
}

impl Encode for i64 {
    fn encode(&self) -> Vec<u8> {
        encode_i64(*self).to_vec()
    }
}

impl Encode for f64 {
    fn encode(&self) -> Vec<u8> {
        encode_f64(*self).to_vec()
    }
}

impl Encode for &str {
    fn encode(&self) -> Vec<u8> {
        encode_txt(self)
    }
}

impl Encode for String {
    fn encode(&self) -> Vec<u8> {
        encode_txt(self)
    }
}

/// Binary data wrapper (to distinguish from text).
#[derive(Debug, Clone)]
pub struct Bin<'a>(pub &'a [u8]);

impl Encode for Bin<'_> {
    fn encode(&self) -> Vec<u8> {
        encode_bin(self.0)
    }
}

/// Map leaf node (contains key-value pairs).
#[derive(Debug, Clone)]
pub struct MapLeaf<'a>(pub &'a [(u32, u32)]);

impl Encode for MapLeaf<'_> {
    fn encode(&self) -> Vec<u8> {
        encode_map_leaf(self.0)
    }
}

/// Map branch node (contains child addresses).
#[derive(Debug, Clone)]
pub struct MapBranch<'a> {
    pub bitmap: u32,
    pub children: &'a [u32],
}

impl Encode for MapBranch<'_> {
    fn encode(&self) -> Vec<u8> {
        encode_map_branch(self.bitmap, self.children)
    }
}

/// Array leaf node.
#[derive(Debug, Clone)]
pub struct ArrLeaf<'a> {
    pub is_root: bool,
    pub shift: u8,
    pub bitmap: u16,
    pub length: Option<u32>,
    pub entries: &'a [u32],
}

impl Encode for ArrLeaf<'_> {
    fn encode(&self) -> Vec<u8> {
        encode_arr_leaf(
            self.is_root,
            self.shift,
            self.bitmap,
            self.length,
            self.entries,
        )
    }
}

/// Array branch node.
#[derive(Debug, Clone)]
pub struct ArrBranch<'a> {
    pub is_root: bool,
    pub shift: u8,
    pub bitmap: u16,
    pub length: Option<u32>,
    pub children: &'a [u32],
}

impl Encode for ArrBranch<'_> {
    fn encode(&self) -> Vec<u8> {
        encode_arr_branch(
            self.is_root,
            self.shift,
            self.bitmap,
            self.length,
            self.children,
        )
    }
}

/// Raw pre-encoded bytes wrapper.
///
/// Use this when you have bytes that are already encoded in TRON format
/// and want to pass them to [`Document::append`](crate::Document::append)
/// or [`Document::from_value`](crate::Document::from_value).
///
/// # Example
///
/// ```
/// use tron::encode::{Raw, encode_i64};
///
/// // Pre-encode a value
/// let bytes = encode_i64(42);
///
/// // Wrap it for use with Document methods
/// let raw = Raw(&bytes);
/// ```
#[derive(Debug, Clone, Copy)]
pub struct Raw<'a>(pub &'a [u8]);

impl Encode for Raw<'_> {
    fn encode(&self) -> Vec<u8> {
        self.0.to_vec()
    }
}

// Implement Encode for fixed-size byte arrays (for convenience in tests)
impl<const N: usize> Encode for [u8; N] {
    fn encode(&self) -> Vec<u8> {
        self.to_vec()
    }
}

impl<const N: usize> Encode for &[u8; N] {
    fn encode(&self) -> Vec<u8> {
        self.to_vec()
    }
}

/// Encode a nil value (1 byte).
#[inline]
#[must_use]
pub fn encode_nil() -> [u8; 1] {
    [Tag::encode_nil()]
}

/// Encode a boolean value (1 byte).
#[inline]
#[must_use]
pub fn encode_bool(value: bool) -> [u8; 1] {
    [Tag::encode_bit(value)]
}

/// Encode an i64 value (9 bytes).
#[inline]
#[must_use]
pub fn encode_i64(value: i64) -> [u8; 9] {
    let mut buf = [0u8; 9];
    buf[0] = Tag::encode_i64();
    buf[1..9].copy_from_slice(&value.to_le_bytes());
    buf
}

/// Encode an f64 value (9 bytes).
#[inline]
#[must_use]
pub fn encode_f64(value: f64) -> [u8; 9] {
    let mut buf = [0u8; 9];
    buf[0] = Tag::encode_f64();
    buf[1..9].copy_from_slice(&value.to_le_bytes());
    buf
}

/// Encode a text string value.
///
/// Uses packed encoding for strings up to 15 bytes, unpacked for longer.
#[must_use]
pub fn encode_txt(s: &str) -> Vec<u8> {
    encode_txt_or_bin(s.as_bytes(), true)
}

/// Encode a binary value.
///
/// Uses packed encoding for data up to 15 bytes, unpacked for longer.
#[must_use]
pub fn encode_bin(data: &[u8]) -> Vec<u8> {
    encode_txt_or_bin(data, false)
}

fn encode_txt_or_bin(data: &[u8], is_txt: bool) -> Vec<u8> {
    let len = data.len();

    if len <= 15 {
        // Packed: length in high nibble of tag
        let mut result = Vec::with_capacity(1 + len);
        let tag = if is_txt {
            Tag::encode_txt_packed(len as u8)
        } else {
            Tag::encode_bin_packed(len as u8)
        };
        result.push(tag);
        result.extend_from_slice(data);
        result
    } else {
        // Unpacked: separate length bytes
        let (n, len_bytes) = minimal_uint_encoding(len);
        let mut result = Vec::with_capacity(1 + n + len);
        let tag = if is_txt {
            Tag::encode_txt_unpacked(n as u8)
        } else {
            Tag::encode_bin_unpacked(n as u8)
        };
        result.push(tag);
        result.extend_from_slice(&len_bytes[..n]);
        result.extend_from_slice(data);
        result
    }
}

/// Encode a map branch node.
///
/// - `bitmap`: 32-bit bitmap indicating which slots are occupied
/// - `child_addrs`: addresses of child nodes, in slot order
#[must_use]
pub fn encode_map_branch(bitmap: u32, child_addrs: &[u32]) -> Vec<u8> {
    // Layout: tag + node_len + bitmap + child_addrs
    // node_len = 1 (tag) + mm (len field) + 4 (bitmap) + 4*n (children)
    let entry_bytes = child_addrs.len() * 4;
    let content_size = 4 + entry_bytes; // bitmap + children (without tag and len field)

    // Calculate total node_len including tag and len field itself
    // We need to find mm such that node_len = 1 + mm + content_size fits in mm bytes
    let (mm, len_bytes) = compute_node_len(1 + content_size);
    let node_len = 1 + mm + content_size;

    let mut result = Vec::with_capacity(node_len);
    let tag = Tag::encode_map(true, (mm - 1) as u8);
    result.push(tag);
    result.extend_from_slice(&len_bytes[..mm]);
    result.extend_from_slice(&bitmap.to_le_bytes());
    for addr in child_addrs {
        result.extend_from_slice(&addr.to_le_bytes());
    }
    result
}

/// Encode a map leaf node.
///
/// - `kv_addrs`: pairs of (`key_addr`, `value_addr`), in key order
#[must_use]
pub fn encode_map_leaf(kv_addrs: &[(u32, u32)]) -> Vec<u8> {
    // Layout: tag + node_len + key/value pairs
    let entry_bytes = kv_addrs.len() * 8;
    let content_size = entry_bytes;

    let (mm, len_bytes) = compute_node_len(1 + content_size);
    let node_len = 1 + mm + content_size;

    let mut result = Vec::with_capacity(node_len);
    let tag = Tag::encode_map(false, (mm - 1) as u8);
    result.push(tag);
    result.extend_from_slice(&len_bytes[..mm]);
    for (key_addr, val_addr) in kv_addrs {
        result.extend_from_slice(&key_addr.to_le_bytes());
        result.extend_from_slice(&val_addr.to_le_bytes());
    }
    result
}

/// Encode an array branch node.
///
/// - `is_root`: true for root node (includes length field)
/// - `shift`: bit shift for index calculation
/// - `bitmap`: 16-bit bitmap indicating which slots are occupied
/// - `length`: array length (required if `is_root`)
/// - `child_addrs`: addresses of child nodes, in slot order
#[must_use]
pub fn encode_arr_branch(
    is_root: bool,
    shift: u8,
    bitmap: u16,
    length: Option<u32>,
    child_addrs: &[u32],
) -> Vec<u8> {
    encode_arr_node(is_root, true, shift, bitmap, length, child_addrs)
}

/// Encode an array leaf node.
///
/// - `is_root`: true for root node (includes length field)
/// - `shift`: bit shift for index calculation (should be 0 for leaf)
/// - `bitmap`: 16-bit bitmap indicating which slots are occupied
/// - `length`: array length (required if `is_root`)
/// - `value_addrs`: addresses of value nodes, in slot order
#[must_use]
pub fn encode_arr_leaf(
    is_root: bool,
    shift: u8,
    bitmap: u16,
    length: Option<u32>,
    value_addrs: &[u32],
) -> Vec<u8> {
    encode_arr_node(is_root, false, shift, bitmap, length, value_addrs)
}

fn encode_arr_node(
    is_root: bool,
    is_branch: bool,
    shift: u8,
    bitmap: u16,
    length: Option<u32>,
    addrs: &[u32],
) -> Vec<u8> {
    // Layout: tag + node_len + shift + bitmap + [length if root] + addrs
    let entry_bytes = addrs.len() * 4;
    let length_bytes = if is_root { 4 } else { 0 };
    let content_size = 1 + 2 + length_bytes + entry_bytes; // shift + bitmap + length + entries

    let (mm, len_bytes) = compute_node_len(1 + content_size);
    let node_len = 1 + mm + content_size;

    let mut result = Vec::with_capacity(node_len);
    let tag = Tag::encode_arr(is_root, is_branch, (mm - 1) as u8);
    result.push(tag);
    result.extend_from_slice(&len_bytes[..mm]);
    result.push(shift);
    result.extend_from_slice(&bitmap.to_le_bytes());
    if is_root {
        result.extend_from_slice(&length.unwrap_or(0).to_le_bytes());
    }
    for addr in addrs {
        result.extend_from_slice(&addr.to_le_bytes());
    }
    result
}

/// Compute `node_len` encoding, accounting for the length field itself.
///
/// Returns (mm, `len_bytes`) where mm is the number of bytes for the length field (1-4).
fn compute_node_len(content_after_len: usize) -> (usize, [u8; 4]) {
    // Try mm=1 first, then 2, 3, 4
    for mm in 1..=4 {
        let total = 1 + mm + content_after_len - 1; // tag + len_field + content
        let (needed, _bytes) = minimal_node_len_encoding(total);
        if needed <= mm {
            return (mm, (total as u32).to_le_bytes());
        }
    }
    // Fallback to 4 bytes
    let total = 1 + 4 + content_after_len - 1;
    (4, (total as u32).to_le_bytes())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_encode_nil() {
        assert_eq!(encode_nil(), [0x00]);
    }

    #[test]
    fn test_encode_bool() {
        assert_eq!(encode_bool(false), [0x01]);
        assert_eq!(encode_bool(true), [0x09]);
    }

    #[test]
    fn test_encode_i64() {
        let encoded = encode_i64(42);
        assert_eq!(encoded[0], 0x02);
        assert_eq!(i64::from_le_bytes(encoded[1..9].try_into().unwrap()), 42);

        let encoded = encode_i64(1234);
        assert_eq!(
            encoded,
            [0x02, 0xD2, 0x04, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
        );
    }

    #[test]
    #[allow(clippy::float_cmp)] // 1.5 is exactly representable in IEEE 754
    fn test_encode_f64() {
        let encoded = encode_f64(1.5);
        assert_eq!(encoded[0], 0x03);
        assert_eq!(f64::from_le_bytes(encoded[1..9].try_into().unwrap()), 1.5);
    }

    #[test]
    fn test_encode_txt_packed() {
        // "hi" -> 0x2C 68 69
        let encoded = encode_txt("hi");
        assert_eq!(encoded, vec![0x2C, 0x68, 0x69]);

        // Empty string
        let encoded = encode_txt("");
        assert_eq!(encoded, vec![0x0C]);
    }

    #[test]
    fn test_encode_txt_unpacked() {
        // 16 chars -> unpacked
        let s = "abcdefghijklmnop";
        let encoded = encode_txt(s);
        assert_eq!(encoded[0], 0x14); // unpacked, n=1
        assert_eq!(encoded[1], 0x10); // length = 16
        assert_eq!(&encoded[2..], s.as_bytes());
    }

    #[test]
    fn test_encode_bin() {
        let encoded = encode_bin(&[0xAA, 0xBB, 0xCC]);
        assert_eq!(encoded, vec![0x3D, 0xAA, 0xBB, 0xCC]);
    }

    #[test]
    fn test_encode_map_leaf_empty() {
        let encoded = encode_map_leaf(&[]);
        assert_eq!(encoded, vec![0x0F, 0x02]); // leaf, node_len=2
    }

    #[test]
    fn test_encode_map_leaf_with_entry() {
        let encoded = encode_map_leaf(&[(0x00, 0x06)]);
        assert_eq!(
            encoded,
            vec![
                0x0F, // leaf tag
                0x0A, // node_len = 10
                0x00, 0x00, 0x00, 0x00, // key addr
                0x06, 0x00, 0x00, 0x00, // value addr
            ]
        );
    }

    #[test]
    fn test_encode_map_branch() {
        // Branch with bitmap 0x0041 (slots 0 and 6) and two children
        let encoded = encode_map_branch(0x0041, &[0x0F, 0x3A]);
        assert_eq!(encoded[0], 0x07); // branch tag
        // node_len = 1 + 1 + 4 + 8 = 14 = 0x0E
        assert_eq!(encoded[1], 0x0E);
        // bitmap
        assert_eq!(&encoded[2..6], &[0x41, 0x00, 0x00, 0x00]);
        // children
        assert_eq!(&encoded[6..10], &[0x0F, 0x00, 0x00, 0x00]);
        assert_eq!(&encoded[10..14], &[0x3A, 0x00, 0x00, 0x00]);
    }

    #[test]
    fn test_encode_arr_leaf_empty_root() {
        let encoded = encode_arr_leaf(true, 0, 0, Some(0), &[]);
        assert_eq!(
            encoded,
            vec![
                0x0E, // root leaf tag
                0x09, // node_len = 9
                0x00, // shift = 0
                0x00, 0x00, // bitmap = 0
                0x00, 0x00, 0x00, 0x00, // length = 0
            ]
        );
    }

    #[test]
    fn test_encode_arr_leaf_with_entries() {
        // Root leaf with 2 entries
        let encoded = encode_arr_leaf(true, 0, 0x0003, Some(2), &[0x1C, 0x25]);
        assert_eq!(encoded[0], 0x0E); // root leaf
        assert_eq!(encoded[1], 0x11); // node_len = 17
        assert_eq!(encoded[2], 0x00); // shift
        assert_eq!(&encoded[3..5], &[0x03, 0x00]); // bitmap
        assert_eq!(&encoded[5..9], &[0x02, 0x00, 0x00, 0x00]); // length
        assert_eq!(&encoded[9..13], &[0x1C, 0x00, 0x00, 0x00]); // entry[0]
        assert_eq!(&encoded[13..17], &[0x25, 0x00, 0x00, 0x00]); // entry[1]
    }

    #[test]
    fn test_encode_arr_child_leaf() {
        // Child leaf (no length field)
        let encoded = encode_arr_leaf(false, 0, 0x0001, None, &[0x10]);
        assert_eq!(encoded[0], 0x4E); // child leaf tag
        assert_eq!(encoded[1], 0x09); // node_len = 9
        assert_eq!(encoded[2], 0x00); // shift
        assert_eq!(&encoded[3..5], &[0x01, 0x00]); // bitmap
        assert_eq!(&encoded[5..9], &[0x10, 0x00, 0x00, 0x00]); // entry
    }
}

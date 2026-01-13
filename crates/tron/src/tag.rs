//! Tag byte parsing and encoding for TRON values.
//!
//! Each TRON value starts with a 1-byte tag header. The bottom 3 bits encode
//! the type (0-7), and the upper 5 bits are type-specific.

/// Value type encoded in the bottom 3 bits of the tag byte.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum ValueType {
    Nil = 0,
    Bit = 1,
    I64 = 2,
    F64 = 3,
    Txt = 4,
    Bin = 5,
    Arr = 6,
    Map = 7,
}

impl ValueType {
    /// Parse value type from the bottom 3 bits of a tag byte.
    #[inline]
    #[must_use]
    pub fn from_tag(tag: u8) -> Self {
        match tag & 0b111 {
            0 => ValueType::Nil,
            1 => ValueType::Bit,
            2 => ValueType::I64,
            3 => ValueType::F64,
            4 => ValueType::Txt,
            5 => ValueType::Bin,
            6 => ValueType::Arr,
            7 => ValueType::Map,
            _ => unreachable!(),
        }
    }

    /// Get the type name as a string (for error messages).
    #[must_use]
    pub fn name(self) -> &'static str {
        match self {
            ValueType::Nil => "nil",
            ValueType::Bit => "bit",
            ValueType::I64 => "i64",
            ValueType::F64 => "f64",
            ValueType::Txt => "txt",
            ValueType::Bin => "bin",
            ValueType::Arr => "arr",
            ValueType::Map => "map",
        }
    }
}

/// Parsed tag byte - cheaply constructed, no allocation.
///
/// This is a thin wrapper that provides methods to extract type-specific
/// information from the tag byte without allocation.
#[derive(Debug, Clone, Copy)]
pub struct Tag(u8);

impl Tag {
    /// Create a Tag from a raw byte.
    #[inline]
    #[must_use]
    pub const fn from_byte(b: u8) -> Self {
        Tag(b)
    }

    /// Get the raw tag byte.
    #[inline]
    #[must_use]
    pub const fn raw(self) -> u8 {
        self.0
    }

    /// Get the value type (bottom 3 bits).
    #[inline]
    #[must_use]
    pub fn value_type(self) -> ValueType {
        ValueType::from_tag(self.0)
    }

    // --- Bit type ---

    /// Get boolean value for bit type (bit 3).
    /// Only valid when `value_type()` == Bit.
    #[inline]
    #[must_use]
    pub fn bit_value(self) -> bool {
        (self.0 >> 3) & 1 == 1
    }

    // --- Txt/Bin types ---

    /// Check if txt/bin uses packed encoding (bit 3).
    /// Only valid when `value_type()` == Txt or Bin.
    #[inline]
    #[must_use]
    pub fn is_packed(self) -> bool {
        (self.0 >> 3) & 1 == 1
    }

    /// Get packed length from high 4 bits (0-15).
    /// Only valid when `is_packed()` == true.
    #[inline]
    #[must_use]
    pub fn packed_length(self) -> u8 {
        self.0 >> 4
    }

    /// Get number of bytes used to encode length (1-8).
    /// Only valid when `is_packed()` == false.
    #[inline]
    #[must_use]
    pub fn length_byte_count(self) -> u8 {
        self.0 >> 4
    }

    // --- Arr type ---

    /// Check if arr is a root node (R bit = 0 means root).
    /// Only valid when `value_type()` == Arr.
    #[inline]
    #[must_use]
    pub fn arr_is_root(self) -> bool {
        (self.0 >> 6) & 1 == 0
    }

    /// Check if arr is a branch node (B bit = 0 means branch).
    /// Only valid when `value_type()` == Arr.
    #[inline]
    #[must_use]
    pub fn arr_is_branch(self) -> bool {
        (self.0 >> 3) & 1 == 0
    }

    /// Check if arr is a leaf node.
    #[inline]
    #[must_use]
    pub fn arr_is_leaf(self) -> bool {
        !self.arr_is_branch()
    }

    // --- Map type ---

    /// Check if map is a branch node (B bit = 0 means branch).
    /// Only valid when `value_type()` == Map.
    #[inline]
    #[must_use]
    pub fn map_is_branch(self) -> bool {
        (self.0 >> 3) & 1 == 0
    }

    /// Check if map is a leaf node.
    #[inline]
    #[must_use]
    pub fn map_is_leaf(self) -> bool {
        !self.map_is_branch()
    }

    // --- Arr/Map shared ---

    /// Get MM value (bits 4-5) which encodes `node_len` byte count - 1.
    /// Returns the number of bytes used for `node_len` field (1-4).
    /// Only valid when `value_type()` == Arr or Map.
    #[inline]
    #[must_use]
    pub fn node_len_byte_count(self) -> usize {
        ((self.0 >> 4) & 0b11) as usize + 1
    }

    // --- Encoding ---

    /// Encode a nil tag.
    #[inline]
    #[must_use]
    pub const fn encode_nil() -> u8 {
        0x00
    }

    /// Encode a bit tag with the given boolean value.
    #[inline]
    #[must_use]
    pub const fn encode_bit(value: bool) -> u8 {
        if value { 0x09 } else { 0x01 }
    }

    /// Encode an i64 tag.
    #[inline]
    #[must_use]
    pub const fn encode_i64() -> u8 {
        0x02
    }

    /// Encode an f64 tag.
    #[inline]
    #[must_use]
    pub const fn encode_f64() -> u8 {
        0x03
    }

    /// Encode a txt tag with packed length (0-15).
    #[inline]
    #[must_use]
    pub const fn encode_txt_packed(len: u8) -> u8 {
        (len << 4) | 0x08 | 0x04 // packed bit + txt type
    }

    /// Encode a txt tag with unpacked length (n = number of length bytes, 1-8).
    #[inline]
    #[must_use]
    pub const fn encode_txt_unpacked(n: u8) -> u8 {
        (n << 4) | 0x04 // no packed bit + txt type
    }

    /// Encode a bin tag with packed length (0-15).
    #[inline]
    #[must_use]
    pub const fn encode_bin_packed(len: u8) -> u8 {
        (len << 4) | 0x08 | 0x05 // packed bit + bin type
    }

    /// Encode a bin tag with unpacked length (n = number of length bytes, 1-8).
    #[inline]
    #[must_use]
    pub const fn encode_bin_unpacked(n: u8) -> u8 {
        (n << 4) | 0x05 // no packed bit + bin type
    }

    /// Encode an arr tag.
    ///
    /// - `is_root`: true for root node (R=0), false for child node (R=1)
    /// - `is_branch`: true for branch node (B=0), false for leaf node (B=1)
    /// - `mm`: `node_len` byte count - 1 (0-3)
    #[inline]
    #[must_use]
    pub const fn encode_arr(is_root: bool, is_branch: bool, mm: u8) -> u8 {
        let r_bit = if is_root { 0 } else { 1 << 6 };
        let b_bit = if is_branch { 0 } else { 1 << 3 };
        let mm_bits = (mm & 0b11) << 4;
        r_bit | mm_bits | b_bit | 0x06 // arr type
    }

    /// Encode a map tag.
    ///
    /// - `is_branch`: true for branch node (B=0), false for leaf node (B=1)
    /// - `mm`: `node_len` byte count - 1 (0-3)
    #[inline]
    #[must_use]
    pub const fn encode_map(is_branch: bool, mm: u8) -> u8 {
        let b_bit = if is_branch { 0 } else { 1 << 3 };
        let mm_bits = (mm & 0b11) << 4;
        mm_bits | b_bit | 0x07 // map type
    }
}

/// Read a little-endian unsigned integer from a byte slice.
/// Returns None if the slice is empty or longer than 8 bytes.
#[must_use]
pub fn read_uint_le(bytes: &[u8]) -> Option<usize> {
    if bytes.is_empty() || bytes.len() > 8 {
        return None;
    }
    let mut buf = [0u8; 8];
    buf[..bytes.len()].copy_from_slice(bytes);
    Some(u64::from_le_bytes(buf) as usize)
}

/// Compute minimal byte count needed to encode a value.
/// Returns (`byte_count`, bytes) where `byte_count` is 1-8.
#[must_use]
pub fn minimal_uint_encoding(value: usize) -> (usize, [u8; 8]) {
    let bytes = (value as u64).to_le_bytes();
    let n = if value == 0 {
        1
    } else {
        8 - ((value as u64).leading_zeros() / 8) as usize
    };
    (n.max(1), bytes)
}

/// Compute minimal byte count for `node_len` encoding (1-4 bytes).
#[must_use]
pub fn minimal_node_len_encoding(value: usize) -> (usize, [u8; 4]) {
    let bytes = (value as u32).to_le_bytes();
    let n = if value == 0 {
        1
    } else {
        4 - ((value as u32).leading_zeros() / 8) as usize
    };
    (n.clamp(1, 4), bytes)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_value_type_parsing() {
        assert_eq!(ValueType::from_tag(0x00), ValueType::Nil);
        assert_eq!(ValueType::from_tag(0x01), ValueType::Bit);
        assert_eq!(ValueType::from_tag(0x09), ValueType::Bit);
        assert_eq!(ValueType::from_tag(0x02), ValueType::I64);
        assert_eq!(ValueType::from_tag(0x03), ValueType::F64);
        assert_eq!(ValueType::from_tag(0x2C), ValueType::Txt); // "hi" packed
        assert_eq!(ValueType::from_tag(0x3D), ValueType::Bin);
        assert_eq!(ValueType::from_tag(0x0E), ValueType::Arr);
        assert_eq!(ValueType::from_tag(0x0F), ValueType::Map);
    }

    #[test]
    fn test_bit_value() {
        assert!(!Tag::from_byte(0x01).bit_value()); // false
        assert!(Tag::from_byte(0x09).bit_value()); // true
    }

    #[test]
    fn test_txt_packed() {
        // "hi" -> 0x2C (packed, len=2)
        let tag = Tag::from_byte(0x2C);
        assert!(tag.is_packed());
        assert_eq!(tag.packed_length(), 2);

        // "abcdefghijklmnop" -> 0x14 0x10 (unpacked, n=1, len=16)
        let tag = Tag::from_byte(0x14);
        assert!(!tag.is_packed());
        assert_eq!(tag.length_byte_count(), 1);
    }

    #[test]
    fn test_arr_flags() {
        // Root leaf: 0x0E = 0b00001110
        let tag = Tag::from_byte(0x0E);
        assert!(tag.arr_is_root());
        assert!(tag.arr_is_leaf());
        assert_eq!(tag.node_len_byte_count(), 1);

        // Root branch: 0x06 = 0b00000110
        let tag = Tag::from_byte(0x06);
        assert!(tag.arr_is_root());
        assert!(tag.arr_is_branch());

        // Child leaf: 0x4E = 0b01001110
        let tag = Tag::from_byte(0x4E);
        assert!(!tag.arr_is_root());
        assert!(tag.arr_is_leaf());
    }

    #[test]
    fn test_map_flags() {
        // Leaf: 0x0F = 0b00001111
        let tag = Tag::from_byte(0x0F);
        assert!(tag.map_is_leaf());
        assert_eq!(tag.node_len_byte_count(), 1);

        // Branch: 0x07 = 0b00000111
        let tag = Tag::from_byte(0x07);
        assert!(tag.map_is_branch());
    }

    #[test]
    fn test_encoding() {
        assert_eq!(Tag::encode_nil(), 0x00);
        assert_eq!(Tag::encode_bit(false), 0x01);
        assert_eq!(Tag::encode_bit(true), 0x09);
        assert_eq!(Tag::encode_i64(), 0x02);
        assert_eq!(Tag::encode_f64(), 0x03);
        assert_eq!(Tag::encode_txt_packed(2), 0x2C);
        assert_eq!(Tag::encode_txt_unpacked(1), 0x14);
        assert_eq!(Tag::encode_bin_packed(3), 0x3D);
        assert_eq!(Tag::encode_arr(true, false, 0), 0x0E); // root leaf
        assert_eq!(Tag::encode_arr(true, true, 0), 0x06); // root branch
        assert_eq!(Tag::encode_arr(false, false, 0), 0x4E); // child leaf
        assert_eq!(Tag::encode_map(false, 0), 0x0F); // leaf
        assert_eq!(Tag::encode_map(true, 0), 0x07); // branch
    }

    #[test]
    fn test_read_uint_le() {
        assert_eq!(read_uint_le(&[0x10]), Some(16));
        assert_eq!(read_uint_le(&[0x00, 0x01]), Some(256));
        assert_eq!(read_uint_le(&[]), None);
    }
}

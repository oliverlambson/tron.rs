//! Zero-copy value views for TRON data.
//!
//! These types are lightweight wrappers around byte slices that read values
//! directly from the underlying bytes on demand, without allocation.
//!
//! # Typed Access
//!
//! Use the [`Value::typed()`] method to get a type-safe enum representation:
//!
//! ```
//! use tron::value::{Value, Typed};
//!
//! let data = [0x02, 0x2A, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]; // i64(42)
//! let value = Value::new(&data, 0).unwrap();
//!
//! match value.typed() {
//!     Typed::I64(n) => assert_eq!(n, 42),
//!     _ => panic!("expected i64"),
//! }
//! ```

use crate::error::{Error, Result};
use crate::tag::{read_uint_le, Tag, ValueType};

/// A typed view of a TRON value for pattern matching.
///
/// This enum allows idiomatic Rust pattern matching over value types:
///
/// ```
/// use tron::value::{Value, Typed};
///
/// fn describe(value: &Value) -> String {
///     match value.typed() {
///         Typed::Nil => "null".to_string(),
///         Typed::Bool(b) => format!("bool: {}", b),
///         Typed::I64(n) => format!("int: {}", n),
///         Typed::F64(n) => format!("float: {}", n),
///         Typed::Str(s) => format!("string: {:?}", s),
///         Typed::Bytes(b) => format!("bytes: {} bytes", b.len()),
///         Typed::Arr(arr) => format!("array: {} entries", arr.entry_count()),
///         Typed::Map(map) => format!("map: {} entries", map.entry_count()),
///     }
/// }
/// ```
#[derive(Debug, Clone)]
pub enum Typed<'a> {
    /// Nil (null) value.
    Nil,
    /// Boolean value.
    Bool(bool),
    /// 64-bit signed integer.
    I64(i64),
    /// 64-bit floating point number.
    F64(f64),
    /// UTF-8 string (zero-copy reference).
    Str(&'a str),
    /// Binary data (zero-copy reference).
    Bytes(&'a [u8]),
    /// Array node.
    Arr(ArrNode<'a>),
    /// Map node.
    Map(MapNode<'a>),
}

/// A zero-copy view into a TRON value at a specific address.
///
/// This does NOT store parsed data - it stores a reference to the document
/// bytes and reads values on demand via accessor methods.
///
/// Size: 24 bytes on 64-bit (16-byte fat pointer + 4-byte addr + padding)
#[derive(Clone, Copy)]
pub struct Value<'a> {
    /// The complete document buffer.
    data: &'a [u8],
    /// Absolute address of this value's tag byte.
    addr: u32,
}

impl<'a> Value<'a> {
    /// Create a new value view at the given address.
    #[inline]
    pub fn new(data: &'a [u8], addr: u32) -> Result<Self> {
        if addr as usize >= data.len() {
            return Err(Error::AddressOutOfBounds {
                addr,
                len: data.len(),
            });
        }
        Ok(Self { data, addr })
    }

    /// Create a value view without bounds checking.
    ///
    /// # Safety
    /// Caller must ensure addr is within bounds.
    #[inline]
    pub unsafe fn new_unchecked(data: &'a [u8], addr: u32) -> Self {
        Self { data, addr }
    }

    /// Get the absolute address of this value's tag byte.
    #[inline]
    pub fn addr(&self) -> u32 {
        self.addr
    }

    /// Get a reference to the underlying document data.
    #[inline]
    pub fn data(&self) -> &'a [u8] {
        self.data
    }

    /// Get the raw tag byte.
    #[inline]
    fn tag(&self) -> Tag {
        Tag::from_byte(self.data[self.addr as usize])
    }

    /// Get a typed view of this value for pattern matching.
    ///
    /// # Example
    ///
    /// ```
    /// use tron::value::{Value, Typed};
    ///
    /// fn process(value: &Value) {
    ///     match value.typed() {
    ///         Typed::Nil => println!("got null"),
    ///         Typed::Bool(b) => println!("got bool: {}", b),
    ///         Typed::I64(n) => println!("got int: {}", n),
    ///         Typed::F64(n) => println!("got float: {}", n),
    ///         Typed::Str(s) => println!("got string: {}", s),
    ///         Typed::Bytes(b) => println!("got {} bytes", b.len()),
    ///         Typed::Arr(arr) => println!("got array with {} items", arr.entry_count()),
    ///         Typed::Map(map) => println!("got map with {} entries", map.entry_count()),
    ///     }
    /// }
    /// ```
    pub fn typed(&self) -> Typed<'a> {
        match self.tag().value_type() {
            ValueType::Nil => Typed::Nil,
            ValueType::Bit => Typed::Bool(self.tag().bit_value()),
            ValueType::I64 => {
                let start = self.addr as usize + 1;
                let bytes: [u8; 8] = self.data[start..start + 8].try_into().unwrap();
                Typed::I64(i64::from_le_bytes(bytes))
            }
            ValueType::F64 => {
                let start = self.addr as usize + 1;
                let bytes: [u8; 8] = self.data[start..start + 8].try_into().unwrap();
                Typed::F64(f64::from_le_bytes(bytes))
            }
            ValueType::Txt => {
                let bytes = self.txt_or_bin_bytes().unwrap_or(&[]);
                let s = std::str::from_utf8(bytes).unwrap_or("");
                Typed::Str(s)
            }
            ValueType::Bin => {
                let bytes = self.txt_or_bin_bytes().unwrap_or(&[]);
                Typed::Bytes(bytes)
            }
            ValueType::Arr => Typed::Arr(ArrNode::new(self.data, self.addr)),
            ValueType::Map => Typed::Map(MapNode::new(self.data, self.addr)),
        }
    }

    /// Internal: parse txt/bin payload bytes.
    fn txt_or_bin_bytes(&self) -> Option<&'a [u8]> {
        let tag = self.tag();
        let base = self.addr as usize;

        if tag.is_packed() {
            let len = tag.packed_length() as usize;
            let start = base + 1;
            self.data.get(start..start + len)
        } else {
            let n = tag.length_byte_count() as usize;
            if n == 0 || n > 8 {
                return None;
            }
            let len_start = base + 1;
            let len = read_uint_le(self.data.get(len_start..len_start + n)?)?;
            let payload_start = len_start + n;
            self.data.get(payload_start..payload_start + len)
        }
    }

    /// Get the total byte size of this value node.
    ///
    /// This is useful for skipping over values or iterating through a buffer.
    pub fn node_size(&self) -> Result<usize> {
        let tag = self.tag();
        let base = self.addr as usize;

        match tag.value_type() {
            ValueType::Nil => Ok(1),
            ValueType::Bit => Ok(1),
            ValueType::I64 => Ok(9), // 1 tag + 8 payload
            ValueType::F64 => Ok(9),
            ValueType::Txt | ValueType::Bin => {
                if tag.is_packed() {
                    Ok(1 + tag.packed_length() as usize)
                } else {
                    let n = tag.length_byte_count() as usize;
                    let len_start = base + 1;
                    let len = read_uint_le(
                        self.data
                            .get(len_start..len_start + n)
                            .ok_or(Error::InvalidLengthEncoding)?,
                    )
                    .ok_or(Error::InvalidLengthEncoding)?;
                    Ok(1 + n + len)
                }
            }
            ValueType::Arr | ValueType::Map => {
                let mm = tag.node_len_byte_count();
                let len_start = base + 1;
                let node_len = read_uint_le(
                    self.data
                        .get(len_start..len_start + mm)
                        .ok_or(Error::InvalidLengthEncoding)?,
                )
                .ok_or(Error::InvalidLengthEncoding)?;
                Ok(node_len)
            }
        }
    }
}

impl<'a> std::fmt::Debug for Value<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.typed() {
            Typed::Nil => write!(f, "Value::Nil"),
            Typed::Bool(b) => write!(f, "Value::Bool({:?})", b),
            Typed::I64(n) => write!(f, "Value::I64({:?})", n),
            Typed::F64(n) => write!(f, "Value::F64({:?})", n),
            Typed::Str(s) => write!(f, "Value::Str({:?})", s),
            Typed::Bytes(b) => write!(f, "Value::Bytes({:?})", b),
            Typed::Arr(_) => write!(f, "Value::Arr(@{:#x})", self.addr),
            Typed::Map(_) => write!(f, "Value::Map(@{:#x})", self.addr),
        }
    }
}

/// Zero-copy view into an array node.
#[derive(Clone, Copy)]
pub struct ArrNode<'a> {
    data: &'a [u8],
    addr: u32,
}

impl<'a> ArrNode<'a> {
    /// Create a new array node view.
    #[inline]
    pub fn new(data: &'a [u8], addr: u32) -> Self {
        Self { data, addr }
    }

    /// Get the absolute address of this node.
    #[inline]
    pub fn addr(&self) -> u32 {
        self.addr
    }

    /// Get the raw tag byte.
    #[inline]
    fn tag(&self) -> Tag {
        Tag::from_byte(self.data[self.addr as usize])
    }

    /// Check if this is a root array node.
    #[inline]
    pub fn is_root(&self) -> bool {
        self.tag().arr_is_root()
    }

    /// Check if this is a branch node.
    #[inline]
    pub fn is_branch(&self) -> bool {
        self.tag().arr_is_branch()
    }

    /// Check if this is a leaf node.
    #[inline]
    pub fn is_leaf(&self) -> bool {
        self.tag().arr_is_leaf()
    }

    /// Get the node length in bytes (including tag and length field).
    pub fn node_len(&self) -> u32 {
        let base = self.addr as usize;
        let mm = self.tag().node_len_byte_count();
        read_uint_le(&self.data[base + 1..base + 1 + mm]).unwrap_or(0) as u32
    }

    /// Get the shift value for index calculation.
    pub fn shift(&self) -> u8 {
        let base = self.addr as usize;
        let mm = self.tag().node_len_byte_count();
        self.data[base + 1 + mm]
    }

    /// Get the bitmap indicating which slots are occupied.
    pub fn bitmap(&self) -> u16 {
        let base = self.addr as usize;
        let mm = self.tag().node_len_byte_count();
        u16::from_le_bytes([self.data[base + 2 + mm], self.data[base + 3 + mm]])
    }

    /// Get the array length (only for root nodes).
    pub fn length(&self) -> Option<u32> {
        if !self.is_root() {
            return None;
        }
        let base = self.addr as usize;
        let mm = self.tag().node_len_byte_count();
        Some(u32::from_le_bytes([
            self.data[base + 4 + mm],
            self.data[base + 5 + mm],
            self.data[base + 6 + mm],
            self.data[base + 7 + mm],
        ]))
    }

    /// Get the byte offset where entries begin.
    fn entries_start(&self) -> usize {
        let base = self.addr as usize;
        let mm = self.tag().node_len_byte_count();
        // Header: tag(1) + node_len(mm) + shift(1) + bitmap(2) + length(4, root only)
        if self.is_root() {
            base + 1 + mm + 1 + 2 + 4
        } else {
            base + 1 + mm + 1 + 2
        }
    }

    /// Get the number of entries (popcount of bitmap).
    #[inline]
    pub fn entry_count(&self) -> usize {
        self.bitmap().count_ones() as usize
    }

    /// Get child/value address at physical index.
    pub fn get_entry_addr(&self, physical_index: usize) -> Option<u32> {
        let offset = self.entries_start() + physical_index * 4;
        if offset + 4 > self.data.len() {
            return None;
        }
        Some(u32::from_le_bytes([
            self.data[offset],
            self.data[offset + 1],
            self.data[offset + 2],
            self.data[offset + 3],
        ]))
    }

    /// Iterator over entry addresses.
    pub fn entry_addrs(&self) -> impl Iterator<Item = u32> + 'a {
        let count = self.entry_count();
        let entries_start = self.entries_start();
        let data = self.data;
        (0..count).filter_map(move |i| {
            let offset = entries_start + i * 4;
            if offset + 4 > data.len() {
                return None;
            }
            Some(u32::from_le_bytes([
                data[offset],
                data[offset + 1],
                data[offset + 2],
                data[offset + 3],
            ]))
        })
    }
}

impl<'a> std::fmt::Debug for ArrNode<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ArrNode")
            .field("addr", &format_args!("{:#x}", self.addr))
            .field("is_root", &self.is_root())
            .field("is_branch", &self.is_branch())
            .field("shift", &self.shift())
            .field("bitmap", &format_args!("{:#06x}", self.bitmap()))
            .field("length", &self.length())
            .field("entry_count", &self.entry_count())
            .finish()
    }
}

/// Zero-copy view into a map node.
#[derive(Clone, Copy)]
pub struct MapNode<'a> {
    data: &'a [u8],
    addr: u32,
}

impl<'a> MapNode<'a> {
    /// Create a new map node view.
    #[inline]
    pub fn new(data: &'a [u8], addr: u32) -> Self {
        Self { data, addr }
    }

    /// Get the absolute address of this node.
    #[inline]
    pub fn addr(&self) -> u32 {
        self.addr
    }

    /// Get the raw tag byte.
    #[inline]
    fn tag(&self) -> Tag {
        Tag::from_byte(self.data[self.addr as usize])
    }

    /// Check if this is a branch node.
    #[inline]
    pub fn is_branch(&self) -> bool {
        self.tag().map_is_branch()
    }

    /// Check if this is a leaf node.
    #[inline]
    pub fn is_leaf(&self) -> bool {
        self.tag().map_is_leaf()
    }

    /// Get the node length in bytes.
    pub fn node_len(&self) -> u32 {
        let base = self.addr as usize;
        let mm = self.tag().node_len_byte_count();
        read_uint_le(&self.data[base + 1..base + 1 + mm]).unwrap_or(0) as u32
    }

    /// Get the bitmap (only for branch nodes).
    pub fn bitmap(&self) -> Option<u32> {
        if !self.is_branch() {
            return None;
        }
        let base = self.addr as usize;
        let mm = self.tag().node_len_byte_count();
        Some(u32::from_le_bytes([
            self.data[base + 1 + mm],
            self.data[base + 2 + mm],
            self.data[base + 3 + mm],
            self.data[base + 4 + mm],
        ]))
    }

    /// Get the byte offset where entries begin.
    fn entries_start(&self) -> usize {
        let base = self.addr as usize;
        let mm = self.tag().node_len_byte_count();
        // Header: tag(1) + node_len(mm) + bitmap(4, branch only)
        if self.is_branch() {
            base + 1 + mm + 4
        } else {
            base + 1 + mm
        }
    }

    /// Get the number of entries.
    pub fn entry_count(&self) -> usize {
        if self.is_branch() {
            self.bitmap().map(|b| b.count_ones() as usize).unwrap_or(0)
        } else {
            // Leaf: calculate from node_len
            let entries_bytes = self.node_len() as usize - (self.entries_start() - self.addr as usize);
            entries_bytes / 8 // 8 bytes per kv pair
        }
    }

    /// Get child address at physical index (branch nodes only).
    pub fn get_child_addr(&self, physical_index: usize) -> Option<u32> {
        if !self.is_branch() {
            return None;
        }
        let offset = self.entries_start() + physical_index * 4;
        if offset + 4 > self.data.len() {
            return None;
        }
        Some(u32::from_le_bytes([
            self.data[offset],
            self.data[offset + 1],
            self.data[offset + 2],
            self.data[offset + 3],
        ]))
    }

    /// Get (key_addr, value_addr) at physical index (leaf nodes only).
    pub fn get_kv_addrs(&self, physical_index: usize) -> Option<(u32, u32)> {
        if self.is_branch() {
            return None;
        }
        let offset = self.entries_start() + physical_index * 8;
        if offset + 8 > self.data.len() {
            return None;
        }
        let key_addr = u32::from_le_bytes([
            self.data[offset],
            self.data[offset + 1],
            self.data[offset + 2],
            self.data[offset + 3],
        ]);
        let val_addr = u32::from_le_bytes([
            self.data[offset + 4],
            self.data[offset + 5],
            self.data[offset + 6],
            self.data[offset + 7],
        ]);
        Some((key_addr, val_addr))
    }

    /// Iterator over key-value address pairs (leaf nodes only).
    pub fn kv_pairs(&self) -> impl Iterator<Item = (u32, u32)> + 'a {
        let count = if self.is_leaf() { self.entry_count() } else { 0 };
        let entries_start = self.entries_start();
        let data = self.data;
        (0..count).filter_map(move |i| {
            let offset = entries_start + i * 8;
            if offset + 8 > data.len() {
                return None;
            }
            let key_addr = u32::from_le_bytes([
                data[offset],
                data[offset + 1],
                data[offset + 2],
                data[offset + 3],
            ]);
            let val_addr = u32::from_le_bytes([
                data[offset + 4],
                data[offset + 5],
                data[offset + 6],
                data[offset + 7],
            ]);
            Some((key_addr, val_addr))
        })
    }

    /// Iterator over child addresses (branch nodes only).
    pub fn child_addrs(&self) -> impl Iterator<Item = u32> + 'a {
        let count = if self.is_branch() { self.entry_count() } else { 0 };
        let entries_start = self.entries_start();
        let data = self.data;
        (0..count).filter_map(move |i| {
            let offset = entries_start + i * 4;
            if offset + 4 > data.len() {
                return None;
            }
            Some(u32::from_le_bytes([
                data[offset],
                data[offset + 1],
                data[offset + 2],
                data[offset + 3],
            ]))
        })
    }
}

impl<'a> std::fmt::Debug for MapNode<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("MapNode")
            .field("addr", &format_args!("{:#x}", self.addr))
            .field("is_branch", &self.is_branch())
            .field("bitmap", &self.bitmap().map(|b| format!("{:#010x}", b)))
            .field("entry_count", &self.entry_count())
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_typed() {
        // Nil (also tests node_size)
        let data = [0x00];
        let v = Value::new(&data, 0).unwrap();
        assert!(matches!(v.typed(), Typed::Nil));
        assert_eq!(v.node_size().unwrap(), 1);

        // Bool false
        let data = [0x01];
        let v = Value::new(&data, 0).unwrap();
        assert!(matches!(v.typed(), Typed::Bool(false)));
        assert_eq!(v.node_size().unwrap(), 1);

        // Bool true
        let data = [0x09];
        let v = Value::new(&data, 0).unwrap();
        assert!(matches!(v.typed(), Typed::Bool(true)));

        // I64
        let data = [0x02, 0x2A, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00];
        let v = Value::new(&data, 0).unwrap();
        assert!(matches!(v.typed(), Typed::I64(42)));
        assert_eq!(v.node_size().unwrap(), 9);

        // F64
        let data = [0x03, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xF8, 0x3F];
        let v = Value::new(&data, 0).unwrap();
        match v.typed() {
            Typed::F64(n) => assert_eq!(n, 1.5),
            _ => panic!("expected F64"),
        }
        assert_eq!(v.node_size().unwrap(), 9);

        // Str (packed)
        let data = [0x2C, 0x68, 0x69]; // "hi"
        let v = Value::new(&data, 0).unwrap();
        assert!(matches!(v.typed(), Typed::Str("hi")));
        assert_eq!(v.node_size().unwrap(), 3);

        // Str (unpacked)
        let mut data = vec![0x14, 0x10]; // tag + len=16
        data.extend_from_slice(b"abcdefghijklmnop");
        let v = Value::new(&data, 0).unwrap();
        assert!(matches!(v.typed(), Typed::Str("abcdefghijklmnop")));
        assert_eq!(v.node_size().unwrap(), 18);

        // Bytes
        let data = [0x3D, 0xAA, 0xBB, 0xCC]; // 3 bytes
        let v = Value::new(&data, 0).unwrap();
        match v.typed() {
            Typed::Bytes(b) => assert_eq!(b, &[0xAA, 0xBB, 0xCC]),
            _ => panic!("expected Bytes"),
        }
        assert_eq!(v.node_size().unwrap(), 4);
    }
}

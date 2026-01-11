//! TRON value and node encoding functions.
//!
//! These functions encode Rust values to TRON bytes, appending to a buffer.
//! Each function returns the address (offset) where the value was written.

/// A value that can be encoded to TRON bytes.
#[derive(Debug, Clone, PartialEq)]
pub enum Value<'a> {
    Nil,
    Bit(bool),
    I64(i64),
    F64(f64),
    Txt(&'a str),
    Bin(&'a [u8]),
}

/// Encode any value. Returns the address where written.
pub fn encode_value(buffer: &mut Vec<u8>, value: Value<'_>) -> u32 {
    match value {
        Value::Nil => encode_nil(buffer),
        Value::Bit(v) => encode_bit(buffer, v),
        Value::I64(v) => encode_i64(buffer, v),
        Value::F64(v) => encode_f64(buffer, v),
        Value::Txt(v) => encode_txt(buffer, v),
        Value::Bin(v) => encode_bin(buffer, v),
    }
}

/// Encode nil value. Returns the address where written.
pub fn encode_nil(buffer: &mut Vec<u8>) -> u32 {
    let addr = buffer.len() as u32;
    buffer.push(0x00); // tag: nil (000)
    addr
}

/// Encode boolean value. Returns the address where written.
pub fn encode_bit(buffer: &mut Vec<u8>, value: bool) -> u32 {
    let addr = buffer.len() as u32;
    // tag: bit (001), value in bit 3
    let tag = if value { 0x09 } else { 0x01 };
    buffer.push(tag);
    addr
}

/// Encode i64 value. Returns the address where written.
pub fn encode_i64(buffer: &mut Vec<u8>, value: i64) -> u32 {
    let addr = buffer.len() as u32;
    buffer.push(0x02); // tag: i64 (010)
    buffer.extend_from_slice(&value.to_le_bytes());
    addr
}

/// Encode f64 value. Returns the address where written.
pub fn encode_f64(buffer: &mut Vec<u8>, value: f64) -> u32 {
    let addr = buffer.len() as u32;
    buffer.push(0x03); // tag: f64 (011)
    buffer.extend_from_slice(&value.to_le_bytes());
    addr
}

/// Encode text string. Uses packed encoding if len <= 15.
/// Returns the address where written.
pub fn encode_txt(buffer: &mut Vec<u8>, value: &str) -> u32 {
    let addr = buffer.len() as u32;
    let bytes = value.as_bytes();
    let len = bytes.len();

    if len <= 15 {
        // Packed: length in high 4 bits, isPacked=1 in bit 3
        // Tag: llllP100 where P=1, llll=len
        let tag = ((len as u8) << 4) | 0x0C; // 0x0C = 0b00001100
        buffer.push(tag);
    } else {
        // Unpacked: N bytes for length, isPacked=0
        // Tag: NNNN0100 where NNNN = bytes needed for length
        let n = bytes_needed_for_length(len);
        let tag = ((n as u8) << 4) | 0x04; // 0x04 = 0b00000100
        buffer.push(tag);
        encode_length_bytes(buffer, len, n);
    }
    buffer.extend_from_slice(bytes);
    addr
}

/// Encode binary data. Uses packed encoding if len <= 15.
/// Returns the address where written.
pub fn encode_bin(buffer: &mut Vec<u8>, value: &[u8]) -> u32 {
    let addr = buffer.len() as u32;
    let len = value.len();

    if len <= 15 {
        // Packed: length in high 4 bits, isPacked=1 in bit 3
        // Tag: llllP101 where P=1, llll=len
        let tag = ((len as u8) << 4) | 0x0D; // 0x0D = 0b00001101
        buffer.push(tag);
    } else {
        // Unpacked: N bytes for length, isPacked=0
        // Tag: NNNN0101 where NNNN = bytes needed for length
        let n = bytes_needed_for_length(len);
        let tag = ((n as u8) << 4) | 0x05; // 0x05 = 0b00000101
        buffer.push(tag);
        encode_length_bytes(buffer, len, n);
    }
    buffer.extend_from_slice(value);
    addr
}

/// Encode array root node. Returns the address where written.
///
/// Tag: 0RMMB110 where R=0 (root), MM = bytes for node_len - 1, B = branch flag
pub fn encode_arr_root(
    buffer: &mut Vec<u8>,
    is_branch: bool,
    shift: u8,
    bitmap: u16,
    length: u32,
    entries: &[u32],
) -> u32 {
    let addr = buffer.len() as u32;

    // Calculate node_len: tag(1) + node_len_bytes(M+1) + shift(1) + bitmap(2) + length(4) + entries(4*n)
    let m = compute_m_for_arr(entries.len(), true);
    let node_len = 1 + (m as usize + 1) + 1 + 2 + 4 + (entries.len() * 4);

    // Tag: 0RMMB110 where R=0 (root), B = branch/leaf
    let b = if is_branch { 0 } else { 1 };
    let tag = (m << 4) | (b << 3) | 0x06;
    buffer.push(tag);

    // Node length
    encode_node_len(buffer, node_len as u32, m);

    // Shift
    buffer.push(shift);

    // Bitmap (u16 LE)
    buffer.extend_from_slice(&bitmap.to_le_bytes());

    // Length (u32 LE) - only for root
    buffer.extend_from_slice(&length.to_le_bytes());

    // Entries (u32 LE each)
    for &entry in entries {
        buffer.extend_from_slice(&entry.to_le_bytes());
    }

    addr
}

/// Encode array child node. Returns the address where written.
///
/// Tag: 1RMMB110 where R=1 (child), MM = bytes for node_len - 1, B = branch flag
pub fn encode_arr_child(
    buffer: &mut Vec<u8>,
    is_branch: bool,
    shift: u8,
    bitmap: u16,
    entries: &[u32],
) -> u32 {
    let addr = buffer.len() as u32;

    // Calculate node_len: tag(1) + node_len_bytes(M+1) + shift(1) + bitmap(2) + entries(4*n)
    let m = compute_m_for_arr(entries.len(), false);
    let node_len = 1 + (m as usize + 1) + 1 + 2 + (entries.len() * 4);

    // Tag: 0RMMB110 where R=1 (child), B = branch/leaf
    let b = if is_branch { 0 } else { 1 };
    let tag = (1 << 6) | (m << 4) | (b << 3) | 0x06;
    buffer.push(tag);

    // Node length
    encode_node_len(buffer, node_len as u32, m);

    // Shift
    buffer.push(shift);

    // Bitmap (u16 LE)
    buffer.extend_from_slice(&bitmap.to_le_bytes());

    // Entries (u32 LE each)
    for &entry in entries {
        buffer.extend_from_slice(&entry.to_le_bytes());
    }

    addr
}

/// Encode map branch node. Returns the address where written.
///
/// Tag: 00MMB111 where B=0 (branch), MM = bytes for node_len - 1
pub fn encode_map_branch(buffer: &mut Vec<u8>, bitmap: u32, entries: &[u32]) -> u32 {
    let addr = buffer.len() as u32;

    // Calculate node_len: tag(1) + node_len_bytes(M+1) + bitmap(4) + entries(4*n)
    let m = compute_m_for_map(entries.len(), true);
    let node_len = 1 + (m as usize + 1) + 4 + (entries.len() * 4);

    // Tag: 00MMB111 where B=0 (branch)
    let tag = (m << 4) | 0x07; // B=0, so just 0x07
    buffer.push(tag);

    // Node length
    encode_node_len(buffer, node_len as u32, m);

    // Bitmap (u32 LE)
    buffer.extend_from_slice(&bitmap.to_le_bytes());

    // Entries (u32 LE each)
    for &entry in entries {
        buffer.extend_from_slice(&entry.to_le_bytes());
    }

    addr
}

/// Encode map leaf node. Returns the address where written.
///
/// Tag: 00MMB111 where B=1 (leaf), MM = bytes for node_len - 1
pub fn encode_map_leaf(buffer: &mut Vec<u8>, pairs: &[(u32, u32)]) -> u32 {
    let addr = buffer.len() as u32;

    // Calculate node_len: tag(1) + node_len_bytes(M+1) + pairs(8*n)
    let m = compute_m_for_map(pairs.len() * 2, false);
    let node_len = 1 + (m as usize + 1) + (pairs.len() * 8);

    // Tag: 00MMB111 where B=1 (leaf)
    let tag = (m << 4) | 0x0F; // B=1, so 0x0F
    buffer.push(tag);

    // Node length
    encode_node_len(buffer, node_len as u32, m);

    // Pairs (key_addr, value_addr as u32 LE each)
    for &(key_addr, value_addr) in pairs {
        buffer.extend_from_slice(&key_addr.to_le_bytes());
        buffer.extend_from_slice(&value_addr.to_le_bytes());
    }

    addr
}

/// Encode and append a footer.
pub fn encode_footer(buffer: &mut Vec<u8>, root_addr: u32, prev_root_addr: u32) {
    buffer.extend_from_slice(&root_addr.to_le_bytes());
    buffer.extend_from_slice(&prev_root_addr.to_le_bytes());
    buffer.extend_from_slice(b"TRON");
}

// === Helper functions ===

/// Compute how many bytes are needed to encode a length value.
pub(crate) fn bytes_needed_for_length(len: usize) -> usize {
    match len {
        0..=0xFF => 1,
        0x100..=0xFFFF => 2,
        0x10000..=0xFFFFFF => 3,
        0x1000000..=0xFFFFFFFF => 4,
        _ => 8,
    }
}

/// Encode length as N little-endian bytes.
pub(crate) fn encode_length_bytes(buffer: &mut Vec<u8>, len: usize, n: usize) {
    let bytes = (len as u64).to_le_bytes();
    buffer.extend_from_slice(&bytes[..n]);
}

/// Compute M value (0-3) for array node_len encoding.
pub(crate) fn compute_m_for_arr(entry_count: usize, is_root: bool) -> u8 {
    // node_len = 1 + (M+1) + 1 + 2 + (if root: 4) + entries*4
    let base = if is_root { 8 } else { 4 };
    let node_len = base + entry_count * 4;
    compute_m(node_len as u32)
}

/// Compute M value (0-3) for map node_len encoding.
pub(crate) fn compute_m_for_map(entry_or_pair_count: usize, is_branch: bool) -> u8 {
    // branch: node_len = 1 + (M+1) + 4 + entries*4
    // leaf: node_len = 1 + (M+1) + pairs*8
    let node_len = if is_branch {
        6 + entry_or_pair_count * 4
    } else {
        2 + (entry_or_pair_count / 2) * 8
    };
    compute_m(node_len as u32)
}

/// Compute M value (0-3) based on node_len.
fn compute_m(node_len: u32) -> u8 {
    match node_len {
        0..=0xFF => 0,
        0x100..=0xFFFF => 1,
        0x10000..=0xFFFFFF => 2,
        _ => 3,
    }
}

/// Encode node_len with M+1 bytes.
pub(crate) fn encode_node_len(buffer: &mut Vec<u8>, node_len: u32, m: u8) {
    let bytes = node_len.to_le_bytes();
    buffer.extend_from_slice(&bytes[..=(m as usize)]);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::ValueNode;

    #[test]
    fn test_encode_nil() {
        let mut buffer = Vec::new();
        let addr = encode_nil(&mut buffer);
        assert_eq!(addr, 0);
        assert_eq!(buffer, vec![0x00]);

        // Round-trip
        let parsed = ValueNode::new(&buffer).unwrap();
        assert_eq!(parsed, ValueNode::Nil);
    }

    #[test]
    fn test_encode_bit_false() {
        let mut buffer = Vec::new();
        let addr = encode_bit(&mut buffer, false);
        assert_eq!(addr, 0);
        assert_eq!(buffer, vec![0x01]);

        let parsed = ValueNode::new(&buffer).unwrap();
        assert_eq!(parsed, ValueNode::Bit(false));
    }

    #[test]
    fn test_encode_bit_true() {
        let mut buffer = Vec::new();
        let addr = encode_bit(&mut buffer, true);
        assert_eq!(addr, 0);
        assert_eq!(buffer, vec![0x09]);

        let parsed = ValueNode::new(&buffer).unwrap();
        assert_eq!(parsed, ValueNode::Bit(true));
    }

    #[test]
    fn test_encode_i64() {
        let mut buffer = Vec::new();
        let addr = encode_i64(&mut buffer, 1234);
        assert_eq!(addr, 0);
        assert_eq!(buffer.len(), 9);
        assert_eq!(buffer[0], 0x02);

        let parsed = ValueNode::new(&buffer).unwrap();
        assert_eq!(parsed, ValueNode::I64(1234));
    }

    #[test]
    fn test_encode_i64_negative() {
        let mut buffer = Vec::new();
        encode_i64(&mut buffer, -42);

        let parsed = ValueNode::new(&buffer).unwrap();
        assert_eq!(parsed, ValueNode::I64(-42));
    }

    #[test]
    fn test_encode_f64() {
        let mut buffer = Vec::new();
        let addr = encode_f64(&mut buffer, 1.5);
        assert_eq!(addr, 0);
        assert_eq!(buffer.len(), 9);
        assert_eq!(buffer[0], 0x03);

        let parsed = ValueNode::new(&buffer).unwrap();
        assert_eq!(parsed, ValueNode::F64(1.5));
    }

    #[test]
    fn test_encode_txt_packed() {
        let mut buffer = Vec::new();
        let addr = encode_txt(&mut buffer, "hi");
        assert_eq!(addr, 0);
        // Packed: tag with len=2, isPacked=1
        assert_eq!(buffer, vec![0x2C, 0x68, 0x69]);

        let parsed = ValueNode::new(&buffer).unwrap();
        assert_eq!(parsed, ValueNode::Txt("hi"));
    }

    #[test]
    fn test_encode_txt_unpacked() {
        let mut buffer = Vec::new();
        let long_str = "0123456789abcdef"; // 16 chars, needs unpacked
        encode_txt(&mut buffer, long_str);

        let parsed = ValueNode::new(&buffer).unwrap();
        assert_eq!(parsed, ValueNode::Txt(long_str));
    }

    #[test]
    fn test_encode_txt_empty() {
        let mut buffer = Vec::new();
        encode_txt(&mut buffer, "");

        let parsed = ValueNode::new(&buffer).unwrap();
        assert_eq!(parsed, ValueNode::Txt(""));
    }

    #[test]
    fn test_encode_bin_packed() {
        let mut buffer = Vec::new();
        let data = [0xAA, 0xBB, 0xCC];
        encode_bin(&mut buffer, &data);

        let parsed = ValueNode::new(&buffer).unwrap();
        assert_eq!(parsed, ValueNode::Bin(&data));
    }

    #[test]
    fn test_encode_bin_unpacked() {
        let mut buffer = Vec::new();
        let data: Vec<u8> = (0..20).collect();
        encode_bin(&mut buffer, &data);

        let parsed = ValueNode::new(&buffer).unwrap();
        assert_eq!(parsed, ValueNode::Bin(&data));
    }

    #[test]
    fn test_encode_footer() {
        let mut buffer = Vec::new();
        encode_footer(&mut buffer, 0x12345678, 0x00000000);

        assert_eq!(buffer.len(), 12);
        assert_eq!(&buffer[8..12], b"TRON");
    }

    #[test]
    fn test_multiple_values() {
        let mut buffer = Vec::new();

        let addr1 = encode_i64(&mut buffer, 42);
        let addr2 = encode_txt(&mut buffer, "hello");
        let addr3 = encode_nil(&mut buffer);

        assert_eq!(addr1, 0);
        assert_eq!(addr2, 9);
        assert_eq!(addr3, 9 + 6); // tag + 5 chars

        // Verify each can be parsed at its address
        let v1 = ValueNode::new(&buffer[addr1 as usize..]).unwrap();
        let v2 = ValueNode::new(&buffer[addr2 as usize..]).unwrap();
        let v3 = ValueNode::new(&buffer[addr3 as usize..]).unwrap();

        assert_eq!(v1, ValueNode::I64(42));
        assert_eq!(v2, ValueNode::Txt("hello"));
        assert_eq!(v3, ValueNode::Nil);
    }
}

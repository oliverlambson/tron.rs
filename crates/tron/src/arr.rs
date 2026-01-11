//! Array (vector trie) traversal and mutation functions.

use crate::encode::{compute_m_for_arr, encode_arr_child, encode_arr_root, encode_node_len};
use crate::value::{ArrChildValue, ArrRootValue, ArrValue, ValueNode};

/// Error type for array operations.
#[derive(Debug, Clone, PartialEq)]
pub enum ArrError {
    IndexOutOfBounds { index: u32, length: u32 },
    InvalidNode { address: u32 },
}

// ============================================================================
// Offset-based read functions (no persistent borrows)
// ============================================================================

/// Array node type.
#[derive(Debug, Clone, Copy, PartialEq)]
enum ArrNodeType {
    RootBranch,
    RootLeaf,
    ChildBranch,
    ChildLeaf,
}

/// Parse array node header, returning (node_type, m, is_root, is_branch, entries_offset).
fn parse_arr_header(buffer: &[u8], addr: u32) -> Option<(ArrNodeType, u8, usize)> {
    let data = buffer.get(addr as usize..)?;
    let tag = *data.first()?;

    // Check it's an array node (tag & 0b111 == 0b110)
    if tag & 0b111 != 0b110 {
        return None;
    }

    let is_branch = (tag >> 3) & 0b1 == 0;
    let m = (tag >> 4) & 0b11;
    let is_root = (tag >> 6) & 0b1 == 0;

    let node_type = match (is_root, is_branch) {
        (true, true) => ArrNodeType::RootBranch,
        (true, false) => ArrNodeType::RootLeaf,
        (false, true) => ArrNodeType::ChildBranch,
        (false, false) => ArrNodeType::ChildLeaf,
    };

    // entries_offset = 1 (tag) + (m+1) (node_len) + 1 (shift) + 2 (bitmap) + if root: 4 (length)
    let entries_offset = 1 + (m as usize + 1) + 1 + 2 + if is_root { 4 } else { 0 };

    Some((node_type, m, entries_offset))
}

/// Get the type of an array node.
fn arr_node_type(buffer: &[u8], addr: u32) -> Option<ArrNodeType> {
    parse_arr_header(buffer, addr).map(|(t, _, _)| t)
}

/// Get the shift of an array node.
fn arr_shift(buffer: &[u8], addr: u32) -> Option<u8> {
    let data = buffer.get(addr as usize..)?;
    let tag = *data.first()?;

    if tag & 0b111 != 0b110 {
        return None;
    }

    let m = ((tag >> 4) & 0b11) as usize;
    let shift_offset = 1 + (m + 1); // after tag and node_len
    data.get(shift_offset).copied()
}

/// Get the bitmap of an array node.
fn arr_bitmap(buffer: &[u8], addr: u32) -> Option<u16> {
    let data = buffer.get(addr as usize..)?;
    let tag = *data.first()?;

    if tag & 0b111 != 0b110 {
        return None;
    }

    let m = ((tag >> 4) & 0b11) as usize;
    let bitmap_offset = 1 + (m + 1) + 1; // after tag, node_len, shift
    let bitmap_bytes = data.get(bitmap_offset..bitmap_offset + 2)?;
    Some(u16::from_le_bytes(bitmap_bytes.try_into().ok()?))
}

/// Get the length of an array root node (only valid for root nodes).
#[allow(dead_code)]
fn arr_length(buffer: &[u8], addr: u32) -> Option<u32> {
    let (node_type, m, _) = parse_arr_header(buffer, addr)?;

    // Only root nodes have length
    if !matches!(node_type, ArrNodeType::RootBranch | ArrNodeType::RootLeaf) {
        return None;
    }

    let data = buffer.get(addr as usize..)?;
    let length_offset = 1 + (m as usize + 1) + 1 + 2; // after tag, node_len, shift, bitmap
    let length_bytes = data.get(length_offset..length_offset + 4)?;
    Some(u32::from_le_bytes(length_bytes.try_into().ok()?))
}

/// Get the number of entries in an array node.
fn arr_entry_count(buffer: &[u8], addr: u32) -> Option<usize> {
    let bitmap = arr_bitmap(buffer, addr)?;
    Some(bitmap.count_ones() as usize)
}

/// Get a specific entry from an array node.
fn arr_entry(buffer: &[u8], addr: u32, index: usize) -> Option<u32> {
    let (_, _m, entries_offset) = parse_arr_header(buffer, addr)?;

    let data = buffer.get(addr as usize..)?;
    let entry_offset = entries_offset + index * 4;
    let entry_bytes = data.get(entry_offset..entry_offset + 4)?;
    Some(u32::from_le_bytes(entry_bytes.try_into().ok()?))
}

/// Check if an array node is a branch.
fn arr_is_branch(buffer: &[u8], addr: u32) -> Option<bool> {
    let node_type = arr_node_type(buffer, addr)?;
    Some(matches!(node_type, ArrNodeType::RootBranch | ArrNodeType::ChildBranch))
}

/// Check if an array node is a root.
#[allow(dead_code)]
fn arr_is_root(buffer: &[u8], addr: u32) -> Option<bool> {
    let node_type = arr_node_type(buffer, addr)?;
    Some(matches!(node_type, ArrNodeType::RootBranch | ArrNodeType::RootLeaf))
}

// ============================================================================
// Helper functions
// ============================================================================

/// Compute slot from index and shift.
/// slot = (index >> shift) & 0xF
fn slot(index: u32, shift: u8) -> u8 {
    ((index >> shift) & 0xF) as u8
}

/// Compute child index from bitmap and slot using popcount.
/// child_index = popcount(bitmap & ((1 << slot) - 1))
fn child_index(bitmap: u16, slot: u8) -> usize {
    (bitmap & ((1u16 << slot) - 1)).count_ones() as usize
}

/// Check if a slot bit is set in the bitmap.
fn bit_set(bitmap: u16, slot: u8) -> bool {
    (bitmap >> slot) & 1 == 1
}

/// Get element at index from array trie.
///
/// # Arguments
/// * `buffer` - The full TRON document buffer
/// * `node_addr` - Address of the array node in the buffer
/// * `index` - Array index to retrieve
/// * `length` - Total array length (from root node)
///
/// # Returns
/// `Some(ValueNode)` if index is valid and element exists, `None` otherwise.
pub fn arr_get<'a>(buffer: &'a [u8], node_addr: u32, index: u32, length: u32) -> Option<ValueNode<'a>> {
    // Bounds check
    if index >= length {
        return None;
    }

    let node_bytes = buffer.get(node_addr as usize..)?;
    let node = ValueNode::new(node_bytes)?;

    match node {
        ValueNode::Arr(arr) => arr_get_node(buffer, &arr, index),
        _ => None,
    }
}

/// Internal recursive traversal for array nodes.
fn arr_get_node<'a>(buffer: &'a [u8], arr: &ArrValue<'a>, index: u32) -> Option<ValueNode<'a>> {
    match arr {
        ArrValue::Root(root) => arr_get_root(buffer, root, index),
        ArrValue::Child(child) => arr_get_child(buffer, child, index),
    }
}

/// Traverse from a root array node.
fn arr_get_root<'a>(buffer: &'a [u8], root: &ArrRootValue<'a>, index: u32) -> Option<ValueNode<'a>> {
    let s = slot(index, root.shift);

    if !bit_set(root.bitmap, s) {
        return None;
    }

    let i = child_index(root.bitmap, s);
    let entries: Vec<u32> = root.entries().collect();
    let child_addr = *entries.get(i)?;

    if root.is_branch {
        // Recurse into child node
        let child_bytes = buffer.get(child_addr as usize..)?;
        let child_node = ValueNode::new(child_bytes)?;
        match child_node {
            ValueNode::Arr(child_arr) => arr_get_node(buffer, &child_arr, index),
            _ => None,
        }
    } else {
        // Leaf node: child_addr points to the value
        let value_bytes = buffer.get(child_addr as usize..)?;
        ValueNode::new(value_bytes)
    }
}

/// Traverse from a child array node.
fn arr_get_child<'a>(buffer: &'a [u8], child: &ArrChildValue<'a>, index: u32) -> Option<ValueNode<'a>> {
    let s = slot(index, child.shift);

    if !bit_set(child.bitmap, s) {
        return None;
    }

    let i = child_index(child.bitmap, s);
    let entries: Vec<u32> = child.entries().collect();
    let child_addr = *entries.get(i)?;

    if child.is_branch {
        // Recurse into child node
        let child_bytes = buffer.get(child_addr as usize..)?;
        let child_node = ValueNode::new(child_bytes)?;
        match child_node {
            ValueNode::Arr(child_arr) => arr_get_node(buffer, &child_arr, index),
            _ => None,
        }
    } else {
        // Leaf node: child_addr points to the value
        let value_bytes = buffer.get(child_addr as usize..)?;
        ValueNode::new(value_bytes)
    }
}

// ============================================================================
// Write functions (copy-on-write)
// ============================================================================

/// Set element at index in array trie, returning new root address.
///
/// This uses copy-on-write semantics: new nodes are appended to the buffer,
/// and ancestors are rebuilt to point to the new nodes.
///
/// # Arguments
/// * `buffer` - Mutable buffer to append new nodes to
/// * `node_addr` - Current root array node address
/// * `index` - Index to update (must be < length)
/// * `value_addr` - Address of the value to set (must already be encoded in buffer)
/// * `length` - Current array length
///
/// # Returns
/// New root address after COW update, or error if index out of bounds.
pub fn arr_set(
    buffer: &mut Vec<u8>,
    node_addr: u32,
    index: u32,
    value_addr: u32,
    length: u32,
) -> Result<u32, ArrError> {
    if index >= length {
        return Err(ArrError::IndexOutOfBounds { index, length });
    }

    arr_set_internal(buffer, node_addr, index, value_addr, length, true)
}

/// Internal recursive set that handles both root and child nodes.
/// Uses offset-based reads and streaming encoding.
fn arr_set_internal(
    buffer: &mut Vec<u8>,
    node_addr: u32,
    index: u32,
    value_addr: u32,
    length: u32,
    is_root_param: bool,
) -> Result<u32, ArrError> {
    // Read node metadata using offset-based functions
    let is_branch =
        arr_is_branch(buffer, node_addr).ok_or(ArrError::InvalidNode { address: node_addr })?;
    let shift =
        arr_shift(buffer, node_addr).ok_or(ArrError::InvalidNode { address: node_addr })?;
    let old_bitmap =
        arr_bitmap(buffer, node_addr).ok_or(ArrError::InvalidNode { address: node_addr })?;
    let old_count =
        arr_entry_count(buffer, node_addr).ok_or(ArrError::InvalidNode { address: node_addr })?;

    let s = slot(index, shift);

    if is_branch {
        // Branch node: recurse into child
        if bit_set(old_bitmap, s) {
            let i = child_index(old_bitmap, s);
            let child_addr = arr_entry(buffer, node_addr, i)
                .ok_or(ArrError::InvalidNode { address: node_addr })?;
            let new_child_addr =
                arr_set_internal(buffer, child_addr, index, value_addr, length, false)?;

            // Stream write new node with updated entry
            if is_root_param {
                stream_arr_root_update(buffer, node_addr, true, shift, old_bitmap, old_count, i, new_child_addr, length)
            } else {
                stream_arr_child_update(buffer, node_addr, true, shift, old_bitmap, old_count, i, new_child_addr)
            }
        } else {
            // Slot not set: create new child leaf
            let new_child_addr = create_leaf_for_value(buffer, index, value_addr, shift - 4);
            let i = child_index(old_bitmap, s);
            let new_bitmap = old_bitmap | (1 << s);

            // Stream write new node with inserted entry
            if is_root_param {
                stream_arr_root_insert(buffer, node_addr, true, shift, new_bitmap, old_count, i, new_child_addr, length)
            } else {
                stream_arr_child_insert(buffer, node_addr, true, shift, new_bitmap, old_count, i, new_child_addr)
            }
        }
    } else {
        // Leaf node: update entry directly
        if bit_set(old_bitmap, s) {
            let i = child_index(old_bitmap, s);

            // Stream write new node with updated entry
            if is_root_param {
                stream_arr_root_update(buffer, node_addr, false, shift, old_bitmap, old_count, i, value_addr, length)
            } else {
                stream_arr_child_update(buffer, node_addr, false, shift, old_bitmap, old_count, i, value_addr)
            }
        } else {
            let i = child_index(old_bitmap, s);
            let new_bitmap = old_bitmap | (1 << s);

            // Stream write new node with inserted entry
            if is_root_param {
                stream_arr_root_insert(buffer, node_addr, false, shift, new_bitmap, old_count, i, value_addr, length)
            } else {
                stream_arr_child_insert(buffer, node_addr, false, shift, new_bitmap, old_count, i, value_addr)
            }
        }
    }
}

/// Stream write an array root node with one entry updated.
#[allow(clippy::too_many_arguments)]
fn stream_arr_root_update(
    buffer: &mut Vec<u8>,
    old_addr: u32,
    is_branch: bool,
    shift: u8,
    bitmap: u16,
    count: usize,
    update_index: usize,
    new_entry: u32,
    length: u32,
) -> Result<u32, ArrError> {
    let m = compute_m_for_arr(count, true);
    let node_len = 1 + (m as usize + 1) + 1 + 2 + 4 + (count * 4);

    let addr = buffer.len() as u32;
    let b = if is_branch { 0 } else { 1 };
    let tag = (m << 4) | (b << 3) | 0x06;
    buffer.push(tag);
    encode_node_len(buffer, node_len as u32, m);
    buffer.push(shift);
    buffer.extend_from_slice(&bitmap.to_le_bytes());
    buffer.extend_from_slice(&length.to_le_bytes());

    // Stream entries, replacing at update_index
    for i in 0..count {
        let entry = if i == update_index {
            new_entry
        } else {
            arr_entry(buffer, old_addr, i).ok_or(ArrError::InvalidNode { address: old_addr })?
        };
        buffer.extend_from_slice(&entry.to_le_bytes());
    }

    Ok(addr)
}

/// Stream write an array child node with one entry updated.
#[allow(clippy::too_many_arguments)]
fn stream_arr_child_update(
    buffer: &mut Vec<u8>,
    old_addr: u32,
    is_branch: bool,
    shift: u8,
    bitmap: u16,
    count: usize,
    update_index: usize,
    new_entry: u32,
) -> Result<u32, ArrError> {
    let m = compute_m_for_arr(count, false);
    let node_len = 1 + (m as usize + 1) + 1 + 2 + (count * 4);

    let addr = buffer.len() as u32;
    let b = if is_branch { 0 } else { 1 };
    let tag = (1 << 6) | (m << 4) | (b << 3) | 0x06;
    buffer.push(tag);
    encode_node_len(buffer, node_len as u32, m);
    buffer.push(shift);
    buffer.extend_from_slice(&bitmap.to_le_bytes());

    // Stream entries, replacing at update_index
    for i in 0..count {
        let entry = if i == update_index {
            new_entry
        } else {
            arr_entry(buffer, old_addr, i).ok_or(ArrError::InvalidNode { address: old_addr })?
        };
        buffer.extend_from_slice(&entry.to_le_bytes());
    }

    Ok(addr)
}

/// Stream write an array root node with one entry inserted.
#[allow(clippy::too_many_arguments)]
fn stream_arr_root_insert(
    buffer: &mut Vec<u8>,
    old_addr: u32,
    is_branch: bool,
    shift: u8,
    new_bitmap: u16,
    old_count: usize,
    insert_index: usize,
    new_entry: u32,
    length: u32,
) -> Result<u32, ArrError> {
    let new_count = old_count + 1;
    let m = compute_m_for_arr(new_count, true);
    let node_len = 1 + (m as usize + 1) + 1 + 2 + 4 + (new_count * 4);

    let addr = buffer.len() as u32;
    let b = if is_branch { 0 } else { 1 };
    let tag = (m << 4) | (b << 3) | 0x06;
    buffer.push(tag);
    encode_node_len(buffer, node_len as u32, m);
    buffer.push(shift);
    buffer.extend_from_slice(&new_bitmap.to_le_bytes());
    buffer.extend_from_slice(&length.to_le_bytes());

    // Stream entries, inserting at insert_index
    let mut old_i = 0;
    for i in 0..new_count {
        let entry = if i == insert_index {
            new_entry
        } else {
            let e = arr_entry(buffer, old_addr, old_i)
                .ok_or(ArrError::InvalidNode { address: old_addr })?;
            old_i += 1;
            e
        };
        buffer.extend_from_slice(&entry.to_le_bytes());
    }

    Ok(addr)
}

/// Stream write an array child node with one entry inserted.
#[allow(clippy::too_many_arguments)]
fn stream_arr_child_insert(
    buffer: &mut Vec<u8>,
    old_addr: u32,
    is_branch: bool,
    shift: u8,
    new_bitmap: u16,
    old_count: usize,
    insert_index: usize,
    new_entry: u32,
) -> Result<u32, ArrError> {
    let new_count = old_count + 1;
    let m = compute_m_for_arr(new_count, false);
    let node_len = 1 + (m as usize + 1) + 1 + 2 + (new_count * 4);

    let addr = buffer.len() as u32;
    let b = if is_branch { 0 } else { 1 };
    let tag = (1 << 6) | (m << 4) | (b << 3) | 0x06;
    buffer.push(tag);
    encode_node_len(buffer, node_len as u32, m);
    buffer.push(shift);
    buffer.extend_from_slice(&new_bitmap.to_le_bytes());

    // Stream entries, inserting at insert_index
    let mut old_i = 0;
    for i in 0..new_count {
        let entry = if i == insert_index {
            new_entry
        } else {
            let e = arr_entry(buffer, old_addr, old_i)
                .ok_or(ArrError::InvalidNode { address: old_addr })?;
            old_i += 1;
            e
        };
        buffer.extend_from_slice(&entry.to_le_bytes());
    }

    Ok(addr)
}

/// Create a new leaf node containing a single value.
fn create_leaf_for_value(buffer: &mut Vec<u8>, index: u32, value_addr: u32, shift: u8) -> u32 {
    let s = slot(index, shift);
    let bitmap = 1u16 << s;
    let entries = [value_addr];

    if shift == 0 {
        encode_arr_child(buffer, false, 0, bitmap, &entries)
    } else {
        // Need to create intermediate nodes
        let child_addr = create_leaf_for_value(buffer, index, value_addr, shift - 4);
        let child_bitmap = 1u16 << slot(index, shift);
        encode_arr_child(buffer, true, shift, child_bitmap, &[child_addr])
    }
}

/// Append values to array, returning new root address and new length.
///
/// # Arguments
/// * `buffer` - Mutable buffer to append new nodes to
/// * `node_addr` - Current root array node address
/// * `values` - Slice of value addresses to append (must already be encoded)
/// * `length` - Current array length
///
/// # Returns
/// Tuple of (new root address, new length) after appending.
pub fn arr_append(
    buffer: &mut Vec<u8>,
    node_addr: u32,
    values: &[u32],
    length: u32,
) -> Result<(u32, u32), ArrError> {
    let mut current_root = node_addr;
    let mut current_length = length;

    for &value_addr in values {
        let new_index = current_length;

        // Check if we need to grow the root using offset-based read
        let current_shift = arr_shift(buffer, current_root)
            .ok_or(ArrError::InvalidNode { address: current_root })?;

        // Check if index fits in current shift
        let needed_shift = shift_for_index(new_index);
        if needed_shift > current_shift {
            // Grow root
            current_root = grow_root(buffer, current_root, needed_shift, current_length)?;
        }

        // Now set the value at new_index
        current_root = arr_set(buffer, current_root, new_index, value_addr, current_length + 1)?;
        current_length += 1;
    }

    Ok((current_root, current_length))
}

/// Calculate minimum shift needed to address an index.
fn shift_for_index(index: u32) -> u8 {
    if index == 0 {
        return 0;
    }
    // Find highest set bit, divide by 4, multiply by 4
    let bits = 32 - index.leading_zeros();
    let shifts_needed = bits.div_ceil(4);
    ((shifts_needed - 1) * 4) as u8
}

/// Grow the root to accommodate a larger shift.
/// Uses offset-based reads and streaming encoding.
fn grow_root(
    buffer: &mut Vec<u8>,
    old_root_addr: u32,
    new_shift: u8,
    length: u32,
) -> Result<u32, ArrError> {
    // Read old root metadata using offset-based functions
    let old_shift =
        arr_shift(buffer, old_root_addr).ok_or(ArrError::InvalidNode { address: old_root_addr })?;
    let old_bitmap =
        arr_bitmap(buffer, old_root_addr).ok_or(ArrError::InvalidNode { address: old_root_addr })?;
    let old_is_branch = arr_is_branch(buffer, old_root_addr)
        .ok_or(ArrError::InvalidNode { address: old_root_addr })?;
    let old_count = arr_entry_count(buffer, old_root_addr)
        .ok_or(ArrError::InvalidNode { address: old_root_addr })?;

    // Stream write the old root as a child node
    let mut child_addr =
        stream_arr_child_copy(buffer, old_root_addr, old_is_branch, old_shift, old_bitmap, old_count)?;
    let mut current_shift = old_shift + 4;

    while current_shift < new_shift {
        // Wrap in another branch at slot 0
        child_addr = encode_arr_child(buffer, true, current_shift, 1, &[child_addr]);
        current_shift += 4;
    }

    // Create new root at new_shift
    Ok(encode_arr_root(buffer, true, new_shift, 1, length, &[child_addr]))
}

/// Stream write an array child node by copying all entries from an existing node.
fn stream_arr_child_copy(
    buffer: &mut Vec<u8>,
    old_addr: u32,
    is_branch: bool,
    shift: u8,
    bitmap: u16,
    count: usize,
) -> Result<u32, ArrError> {
    let m = compute_m_for_arr(count, false);
    let node_len = 1 + (m as usize + 1) + 1 + 2 + (count * 4);

    let addr = buffer.len() as u32;
    let b = if is_branch { 0 } else { 1 };
    let tag = (1 << 6) | (m << 4) | (b << 3) | 0x06;
    buffer.push(tag);
    encode_node_len(buffer, node_len as u32, m);
    buffer.push(shift);
    buffer.extend_from_slice(&bitmap.to_le_bytes());

    // Stream copy all entries
    for i in 0..count {
        let entry =
            arr_entry(buffer, old_addr, i).ok_or(ArrError::InvalidNode { address: old_addr })?;
        buffer.extend_from_slice(&entry.to_le_bytes());
    }

    Ok(addr)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_slot() {
        // index=0, shift=0 -> slot=0
        assert_eq!(slot(0, 0), 0);
        // index=5, shift=0 -> slot=5
        assert_eq!(slot(5, 0), 5);
        // index=16, shift=0 -> slot=0 (16 & 0xF = 0)
        assert_eq!(slot(16, 0), 0);
        // index=17, shift=0 -> slot=1
        assert_eq!(slot(17, 0), 1);
        // index=16, shift=4 -> slot=1 (16 >> 4 = 1)
        assert_eq!(slot(16, 4), 1);
        // index=0x123, shift=4 -> slot=2
        assert_eq!(slot(0x123, 4), 2);
    }

    #[test]
    fn test_child_index() {
        // bitmap=0b1111 (slots 0,1,2,3), slot=2 -> index=2
        assert_eq!(child_index(0b1111, 2), 2);
        // bitmap=0b1010 (slots 1,3), slot=3 -> index=1
        assert_eq!(child_index(0b1010, 3), 1);
        // bitmap=0b1010 (slots 1,3), slot=1 -> index=0
        assert_eq!(child_index(0b1010, 1), 0);
        // bitmap=0b11 (slots 0,1), slot=0 -> index=0
        assert_eq!(child_index(0b11, 0), 0);
        // bitmap=0b11 (slots 0,1), slot=1 -> index=1
        assert_eq!(child_index(0b11, 1), 1);
    }

    #[test]
    fn test_arr_get_single_element() {
        // Build a simple single-element array: [42]
        // Structure:
        //   0x00: i64 value 42
        //   0x09: arr root leaf, length=1, bitmap=0b1, entry -> @0x00
        //   footer at end
        let buffer = vec![
            // 0x00: i64 value 42
            0x02, // tag: i64
            0x2A, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // 42 in little-endian
            // 0x09: arr root leaf
            0x0E, // tag: arr, root, leaf, M=0
            0x0D, // node_len=13
            0x00, // shift=0
            0x01, 0x00, // bitmap=0b1 (slot 0)
            0x01, 0x00, 0x00, 0x00, // length=1
            0x00, 0x00, 0x00, 0x00, // entry[0] -> @0x00
            // footer
            0x09, 0x00, 0x00, 0x00, // root_node_offset: 0x09
            0x00, 0x00, 0x00, 0x00, // prev_root: 0
            b'T', b'R', b'O', b'N',
        ];

        let result = arr_get(&buffer, 0x09, 0, 1);
        assert_eq!(result, Some(ValueNode::I64(42)));

        // Out of bounds
        let result = arr_get(&buffer, 0x09, 1, 1);
        assert_eq!(result, None);
    }

    #[test]
    fn test_arr_get_two_elements() {
        // Array: [10, 20]
        let buffer = vec![
            // 0x00: i64 value 10
            0x02, 0x0A, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            // 0x09: i64 value 20
            0x02, 0x14, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            // 0x12: arr root leaf
            0x0E, // tag: arr, root, leaf, M=0
            0x11, // node_len=17
            0x00, // shift=0
            0x03, 0x00, // bitmap=0b11 (slots 0,1)
            0x02, 0x00, 0x00, 0x00, // length=2
            0x00, 0x00, 0x00, 0x00, // entry[0] -> @0x00
            0x09, 0x00, 0x00, 0x00, // entry[1] -> @0x09
            // footer
            0x12, 0x00, 0x00, 0x00, // root_node_offset: 0x12
            0x00, 0x00, 0x00, 0x00, // prev_root: 0
            b'T', b'R', b'O', b'N',
        ];

        assert_eq!(arr_get(&buffer, 0x12, 0, 2), Some(ValueNode::I64(10)));
        assert_eq!(arr_get(&buffer, 0x12, 1, 2), Some(ValueNode::I64(20)));
        assert_eq!(arr_get(&buffer, 0x12, 2, 2), None);
    }

    #[test]
    fn test_shift_for_index() {
        assert_eq!(shift_for_index(0), 0);
        assert_eq!(shift_for_index(1), 0);
        assert_eq!(shift_for_index(15), 0);
        assert_eq!(shift_for_index(16), 4);
        assert_eq!(shift_for_index(255), 4);
        assert_eq!(shift_for_index(256), 8);
    }

    #[test]
    fn test_arr_set_single_element() {
        use crate::encode::{encode_arr_root, encode_i64};

        // Create initial array [42]
        let mut buffer = Vec::new();
        let val_addr = encode_i64(&mut buffer, 42);
        let root_addr = encode_arr_root(&mut buffer, false, 0, 0b1, 1, &[val_addr]);

        // Verify initial state
        assert_eq!(arr_get(&buffer, root_addr, 0, 1), Some(ValueNode::I64(42)));

        // Update to [100]
        let new_val_addr = encode_i64(&mut buffer, 100);
        let new_root_addr = arr_set(&mut buffer, root_addr, 0, new_val_addr, 1).unwrap();

        // Verify new state
        assert_eq!(arr_get(&buffer, new_root_addr, 0, 1), Some(ValueNode::I64(100)));

        // Old root still works (COW)
        assert_eq!(arr_get(&buffer, root_addr, 0, 1), Some(ValueNode::I64(42)));
    }

    #[test]
    fn test_arr_set_two_elements() {
        use crate::encode::{encode_arr_root, encode_i64};

        // Create initial array [10, 20]
        let mut buffer = Vec::new();
        let val0 = encode_i64(&mut buffer, 10);
        let val1 = encode_i64(&mut buffer, 20);
        let root_addr = encode_arr_root(&mut buffer, false, 0, 0b11, 2, &[val0, val1]);

        // Update index 1 to 99
        let new_val = encode_i64(&mut buffer, 99);
        let new_root = arr_set(&mut buffer, root_addr, 1, new_val, 2).unwrap();

        // Verify
        assert_eq!(arr_get(&buffer, new_root, 0, 2), Some(ValueNode::I64(10)));
        assert_eq!(arr_get(&buffer, new_root, 1, 2), Some(ValueNode::I64(99)));
    }

    #[test]
    fn test_arr_set_out_of_bounds() {
        use crate::encode::{encode_arr_root, encode_i64};

        let mut buffer = Vec::new();
        let val_addr = encode_i64(&mut buffer, 42);
        let root_addr = encode_arr_root(&mut buffer, false, 0, 0b1, 1, &[val_addr]);

        let result = arr_set(&mut buffer, root_addr, 5, val_addr, 1);
        assert_eq!(result, Err(ArrError::IndexOutOfBounds { index: 5, length: 1 }));
    }

    #[test]
    fn test_arr_append_single() {
        use crate::encode::{encode_arr_root, encode_i64};

        // Create initial array [10]
        let mut buffer = Vec::new();
        let val0 = encode_i64(&mut buffer, 10);
        let root_addr = encode_arr_root(&mut buffer, false, 0, 0b1, 1, &[val0]);

        // Append 20
        let val1 = encode_i64(&mut buffer, 20);
        let (new_root, new_len) = arr_append(&mut buffer, root_addr, &[val1], 1).unwrap();

        assert_eq!(new_len, 2);
        assert_eq!(arr_get(&buffer, new_root, 0, 2), Some(ValueNode::I64(10)));
        assert_eq!(arr_get(&buffer, new_root, 1, 2), Some(ValueNode::I64(20)));
    }

    #[test]
    fn test_arr_append_multiple() {
        use crate::encode::{encode_arr_root, encode_i64};

        // Create initial array [1]
        let mut buffer = Vec::new();
        let val0 = encode_i64(&mut buffer, 1);
        let root_addr = encode_arr_root(&mut buffer, false, 0, 0b1, 1, &[val0]);

        // Append [2, 3, 4]
        let val1 = encode_i64(&mut buffer, 2);
        let val2 = encode_i64(&mut buffer, 3);
        let val3 = encode_i64(&mut buffer, 4);
        let (new_root, new_len) = arr_append(&mut buffer, root_addr, &[val1, val2, val3], 1).unwrap();

        assert_eq!(new_len, 4);
        assert_eq!(arr_get(&buffer, new_root, 0, 4), Some(ValueNode::I64(1)));
        assert_eq!(arr_get(&buffer, new_root, 1, 4), Some(ValueNode::I64(2)));
        assert_eq!(arr_get(&buffer, new_root, 2, 4), Some(ValueNode::I64(3)));
        assert_eq!(arr_get(&buffer, new_root, 3, 4), Some(ValueNode::I64(4)));
    }
}

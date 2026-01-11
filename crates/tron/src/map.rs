//! Map (HAMT) traversal and mutation functions.

use crate::encode::{
    compute_m_for_map, encode_map_branch, encode_map_leaf, encode_node_len, encode_value, Value,
};
use crate::value::{MapBranchValue, MapLeafValue, MapValue, ValueNode};
use crate::xxh32::xxh32;

/// Maximum depth for HAMT (32 bits / 4 bits per level = 8 levels, 0-indexed = 7 max)
const MAX_DEPTH: u8 = 7;

/// Error type for map operations.
#[derive(Debug, Clone, PartialEq)]
pub enum MapError {
    InvalidNode { address: u32 },
}

// ============================================================================
// Offset-based read functions (no persistent borrows)
// ============================================================================

/// Map node type.
#[derive(Debug, Clone, Copy, PartialEq)]
enum MapNodeType {
    Branch,
    Leaf,
}

/// Parse map node header, returning (node_type, m, entries_offset).
/// m is the number of extra bytes for node_len (0-3).
/// entries_offset is the byte offset from node_addr to the first entry.
fn parse_map_header(buffer: &[u8], addr: u32) -> Option<(MapNodeType, u8, usize)> {
    let data = buffer.get(addr as usize..)?;
    let tag = *data.first()?;

    // Check it's a map node (tag & 0b111 == 0b111)
    if tag & 0b111 != 0b111 {
        return None;
    }

    let m = (tag >> 4) & 0b11;
    let is_branch = (tag >> 3) & 0b1 == 0;
    let node_type = if is_branch {
        MapNodeType::Branch
    } else {
        MapNodeType::Leaf
    };

    // entries_offset = 1 (tag) + (m+1) (node_len) + if branch: 4 (bitmap)
    let entries_offset = 1 + (m as usize + 1) + if is_branch { 4 } else { 0 };

    Some((node_type, m, entries_offset))
}

/// Get the type of a map node.
fn map_node_type(buffer: &[u8], addr: u32) -> Option<MapNodeType> {
    parse_map_header(buffer, addr).map(|(t, _, _)| t)
}

/// Get the bitmap of a map branch node.
fn map_branch_bitmap(buffer: &[u8], addr: u32) -> Option<u32> {
    let data = buffer.get(addr as usize..)?;
    let tag = *data.first()?;

    if tag & 0b111 != 0b111 {
        return None;
    }
    let is_branch = (tag >> 3) & 0b1 == 0;
    if !is_branch {
        return None;
    }

    let m = ((tag >> 4) & 0b11) as usize;
    let bitmap_offset = 1 + (m + 1); // after tag and node_len
    let bitmap_bytes = data.get(bitmap_offset..bitmap_offset + 4)?;
    Some(u32::from_le_bytes(bitmap_bytes.try_into().ok()?))
}

/// Get the number of entries in a map branch node.
fn map_branch_entry_count(buffer: &[u8], addr: u32) -> Option<usize> {
    let bitmap = map_branch_bitmap(buffer, addr)?;
    Some(bitmap.count_ones() as usize)
}

/// Get a specific entry from a map branch node.
fn map_branch_entry(buffer: &[u8], addr: u32, index: usize) -> Option<u32> {
    let (node_type, _m, entries_offset) = parse_map_header(buffer, addr)?;
    if node_type != MapNodeType::Branch {
        return None;
    }

    let data = buffer.get(addr as usize..)?;
    let entry_offset = entries_offset + index * 4;
    let entry_bytes = data.get(entry_offset..entry_offset + 4)?;
    Some(u32::from_le_bytes(entry_bytes.try_into().ok()?))
}

/// Get the number of pairs in a map leaf node.
fn map_leaf_pair_count(buffer: &[u8], addr: u32) -> Option<usize> {
    let (node_type, m, _entries_offset) = parse_map_header(buffer, addr)?;
    if node_type != MapNodeType::Leaf {
        return None;
    }

    let data = buffer.get(addr as usize..)?;
    let _tag = *data.first()?;

    // Read node_len to compute pair count
    let n = (m as usize) + 1;
    let mut node_len_buf = [0u8; 4];
    node_len_buf[..n].copy_from_slice(data.get(1..1 + n)?);
    let node_len = u32::from_le_bytes(node_len_buf) as usize;

    // node_len = 1 (tag) + (m+1) (node_len bytes) + pairs*8
    // pairs = (node_len - 1 - (m+1)) / 8
    let pairs = (node_len - 1 - n) / 8;
    Some(pairs)
}

/// Get a specific pair from a map leaf node.
fn map_leaf_pair(buffer: &[u8], addr: u32, index: usize) -> Option<(u32, u32)> {
    let (node_type, _, entries_offset) = parse_map_header(buffer, addr)?;
    if node_type != MapNodeType::Leaf {
        return None;
    }

    let data = buffer.get(addr as usize..)?;
    let pair_offset = entries_offset + index * 8;
    let pair_bytes = data.get(pair_offset..pair_offset + 8)?;
    let key_addr = u32::from_le_bytes(pair_bytes[0..4].try_into().ok()?);
    let value_addr = u32::from_le_bytes(pair_bytes[4..8].try_into().ok()?);
    Some((key_addr, value_addr))
}

/// Compute slot from hash and depth.
/// slot = (hash >> (depth * 4)) & 0xF
fn slot(hash: u32, depth: u8) -> u8 {
    ((hash >> (depth * 4)) & 0xF) as u8
}

/// Compute child index from bitmap and slot using popcount.
/// child_index = popcount(bitmap & ((1 << slot) - 1))
fn child_index(bitmap: u32, slot: u8) -> usize {
    (bitmap & ((1u32 << slot) - 1)).count_ones() as usize
}

/// Check if a slot bit is set in the bitmap.
fn bit_set(bitmap: u32, slot: u8) -> bool {
    (bitmap >> slot) & 1 == 1
}

/// Get value for key from map HAMT.
///
/// # Arguments
/// * `buffer` - The full TRON document buffer
/// * `node_addr` - Address of the map node in the buffer
/// * `key` - Key to look up
///
/// # Returns
/// `Some(ValueNode)` if key exists, `None` otherwise.
pub fn map_get<'a>(buffer: &'a [u8], node_addr: u32, key: &str) -> Option<ValueNode<'a>> {
    map_get_depth(buffer, node_addr, key, 0)
}

/// Internal recursive traversal with depth tracking.
fn map_get_depth<'a>(buffer: &'a [u8], node_addr: u32, key: &str, depth: u8) -> Option<ValueNode<'a>> {
    let node_bytes = buffer.get(node_addr as usize..)?;
    let node = ValueNode::new(node_bytes)?;

    match node {
        ValueNode::Map(map) => map_get_node(buffer, &map, key, depth),
        _ => None,
    }
}

/// Traverse a map node (branch or leaf).
fn map_get_node<'a>(buffer: &'a [u8], map: &MapValue<'a>, key: &str, depth: u8) -> Option<ValueNode<'a>> {
    match map {
        MapValue::Branch(branch) => map_get_branch(buffer, branch, key, depth),
        MapValue::Leaf(leaf) => map_get_leaf(buffer, leaf, key),
    }
}

/// Traverse a branch node.
fn map_get_branch<'a>(buffer: &'a [u8], branch: &MapBranchValue<'a>, key: &str, depth: u8) -> Option<ValueNode<'a>> {
    let hash = xxh32(key.as_bytes(), 0);
    let s = slot(hash, depth);

    if !bit_set(branch.bitmap, s) {
        return None;
    }

    let i = child_index(branch.bitmap, s);
    let entries: Vec<u32> = branch
        .entries_buffer
        .chunks_exact(4)
        .map(|c| u32::from_le_bytes([c[0], c[1], c[2], c[3]]))
        .collect();
    let child_addr = *entries.get(i)?;

    // Recurse into child node
    map_get_depth(buffer, child_addr, key, depth + 1)
}

/// Search a leaf node for the key.
fn map_get_leaf<'a>(buffer: &'a [u8], leaf: &MapLeafValue<'a>, key: &str) -> Option<ValueNode<'a>> {
    // Linear search through key/value pairs
    for (key_addr, value_addr) in leaf.pairs() {
        let key_bytes = buffer.get(key_addr as usize..)?;
        let key_node = ValueNode::new(key_bytes)?;

        if let ValueNode::Txt(stored_key) = key_node
            && stored_key == key
        {
            let value_bytes = buffer.get(value_addr as usize..)?;
            return ValueNode::new(value_bytes);
        }
    }

    None
}

// ============================================================================
// Write functions (copy-on-write)
// ============================================================================

/// Set key-value in map HAMT, returning new root address.
///
/// This uses copy-on-write semantics: new nodes are appended to the buffer,
/// and ancestors are rebuilt to point to the new nodes.
///
/// # Arguments
/// * `buffer` - Mutable buffer to append new nodes to
/// * `node_addr` - Current root map node address
/// * `key` - The key string
/// * `value` - The value to set
///
/// # Returns
/// New root address after COW update.
pub fn map_set(
    buffer: &mut Vec<u8>,
    node_addr: u32,
    key: &str,
    value: Value<'_>,
) -> Result<u32, MapError> {
    let key_addr = encode_value(buffer, Value::Txt(key));
    let value_addr = encode_value(buffer, value);
    let hash = xxh32(key.as_bytes(), 0);
    map_set_depth(buffer, node_addr, key_addr, value_addr, key, hash, 0)
}

/// Internal recursive set with depth tracking.
fn map_set_depth(
    buffer: &mut Vec<u8>,
    node_addr: u32,
    key_addr: u32,
    value_addr: u32,
    key_str: &str,
    hash: u32,
    depth: u8,
) -> Result<u32, MapError> {
    let node_type =
        map_node_type(buffer, node_addr).ok_or(MapError::InvalidNode { address: node_addr })?;

    match node_type {
        MapNodeType::Branch => {
            map_set_branch(buffer, node_addr, key_addr, value_addr, key_str, hash, depth)
        }
        MapNodeType::Leaf => {
            map_set_leaf(buffer, node_addr, key_addr, value_addr, key_str, hash, depth)
        }
    }
}

/// Set in a branch node using streaming encoding.
fn map_set_branch(
    buffer: &mut Vec<u8>,
    old_addr: u32,
    key_addr: u32,
    value_addr: u32,
    key_str: &str,
    hash: u32,
    depth: u8,
) -> Result<u32, MapError> {
    let s = slot(hash, depth);

    // Read old node metadata
    let old_bitmap =
        map_branch_bitmap(buffer, old_addr).ok_or(MapError::InvalidNode { address: old_addr })?;
    let old_count = map_branch_entry_count(buffer, old_addr)
        .ok_or(MapError::InvalidNode { address: old_addr })?;

    if bit_set(old_bitmap, s) {
        // Slot exists: recurse into child, then stream with updated entry
        let i = child_index(old_bitmap, s);
        let child_addr = map_branch_entry(buffer, old_addr, i)
            .ok_or(MapError::InvalidNode { address: old_addr })?;
        let new_child_addr =
            map_set_depth(buffer, child_addr, key_addr, value_addr, key_str, hash, depth + 1)?;

        // Stream write new branch with updated entry
        stream_map_branch_update(buffer, old_addr, old_bitmap, old_count, i, new_child_addr)
    } else {
        // Slot empty: create new leaf, then stream with inserted entry
        let new_leaf_addr = encode_map_leaf(buffer, &[(key_addr, value_addr)]);
        let i = child_index(old_bitmap, s);
        let new_bitmap = old_bitmap | (1 << s);

        // Stream write new branch with inserted entry
        stream_map_branch_insert(buffer, old_addr, new_bitmap, old_count, i, new_leaf_addr)
    }
}

/// Stream write a map branch with one entry updated.
fn stream_map_branch_update(
    buffer: &mut Vec<u8>,
    old_addr: u32,
    bitmap: u32,
    count: usize,
    update_index: usize,
    new_entry: u32,
) -> Result<u32, MapError> {
    let m = compute_m_for_map(count, true);
    let node_len = 1 + (m as usize + 1) + 4 + (count * 4);

    let addr = buffer.len() as u32;
    let tag = (m << 4) | 0x07;
    buffer.push(tag);
    encode_node_len(buffer, node_len as u32, m);
    buffer.extend_from_slice(&bitmap.to_le_bytes());

    // Stream entries, replacing at update_index
    for i in 0..count {
        let entry = if i == update_index {
            new_entry
        } else {
            map_branch_entry(buffer, old_addr, i)
                .ok_or(MapError::InvalidNode { address: old_addr })?
        };
        buffer.extend_from_slice(&entry.to_le_bytes());
    }

    Ok(addr)
}

/// Stream write a map branch with one entry inserted.
fn stream_map_branch_insert(
    buffer: &mut Vec<u8>,
    old_addr: u32,
    new_bitmap: u32,
    old_count: usize,
    insert_index: usize,
    new_entry: u32,
) -> Result<u32, MapError> {
    let new_count = old_count + 1;
    let m = compute_m_for_map(new_count, true);
    let node_len = 1 + (m as usize + 1) + 4 + (new_count * 4);

    let addr = buffer.len() as u32;
    let tag = (m << 4) | 0x07;
    buffer.push(tag);
    encode_node_len(buffer, node_len as u32, m);
    buffer.extend_from_slice(&new_bitmap.to_le_bytes());

    // Stream entries, inserting at insert_index
    let mut old_i = 0;
    for i in 0..new_count {
        let entry = if i == insert_index {
            new_entry
        } else {
            let e = map_branch_entry(buffer, old_addr, old_i)
                .ok_or(MapError::InvalidNode { address: old_addr })?;
            old_i += 1;
            e
        };
        buffer.extend_from_slice(&entry.to_le_bytes());
    }

    Ok(addr)
}

/// Set in a leaf node using offset-based reads and streaming encoding.
fn map_set_leaf(
    buffer: &mut Vec<u8>,
    old_addr: u32,
    key_addr: u32,
    value_addr: u32,
    key_str: &str,
    hash: u32,
    depth: u8,
) -> Result<u32, MapError> {
    let pair_count =
        map_leaf_pair_count(buffer, old_addr).ok_or(MapError::InvalidNode { address: old_addr })?;

    // Check if key already exists by reading keys one at a time
    for i in 0..pair_count {
        let (existing_key_addr, _existing_value_addr) = map_leaf_pair(buffer, old_addr, i)
            .ok_or(MapError::InvalidNode { address: old_addr })?;

        // Read the key string
        let key_bytes = buffer
            .get(existing_key_addr as usize..)
            .ok_or(MapError::InvalidNode {
                address: existing_key_addr,
            })?;
        let key_node = ValueNode::new(key_bytes).ok_or(MapError::InvalidNode {
            address: existing_key_addr,
        })?;

        if let ValueNode::Txt(existing_key) = key_node
            && existing_key == key_str
        {
            // Key exists: stream write new leaf with updated value
            return stream_map_leaf_update(
                buffer,
                old_addr,
                pair_count,
                i,
                existing_key_addr,
                value_addr,
            );
        }
    }

    // Key doesn't exist
    if depth == MAX_DEPTH {
        // At max depth: add to collision bucket (sorted by key bytes)
        // Find insert position by comparing keys
        let insert_pos = find_leaf_insert_position(buffer, old_addr, pair_count, key_str)?;
        stream_map_leaf_insert(buffer, old_addr, pair_count, insert_pos, key_addr, value_addr)
    } else {
        // Not at max depth: split into branch
        split_leaf_to_branch(buffer, old_addr, pair_count, key_addr, value_addr, hash, depth)
    }
}

/// Find insert position in a sorted leaf (for collision buckets at max depth).
fn find_leaf_insert_position(
    buffer: &[u8],
    old_addr: u32,
    pair_count: usize,
    key_str: &str,
) -> Result<usize, MapError> {
    for i in 0..pair_count {
        let (existing_key_addr, _) = map_leaf_pair(buffer, old_addr, i)
            .ok_or(MapError::InvalidNode { address: old_addr })?;

        let key_bytes = buffer
            .get(existing_key_addr as usize..)
            .ok_or(MapError::InvalidNode {
                address: existing_key_addr,
            })?;
        let key_node = ValueNode::new(key_bytes).ok_or(MapError::InvalidNode {
            address: existing_key_addr,
        })?;

        if let ValueNode::Txt(existing_key) = key_node
            && existing_key > key_str
        {
            return Ok(i);
        }
    }
    Ok(pair_count)
}

/// Stream write a map leaf with one pair's value updated.
fn stream_map_leaf_update(
    buffer: &mut Vec<u8>,
    old_addr: u32,
    pair_count: usize,
    update_index: usize,
    key_addr: u32,
    new_value_addr: u32,
) -> Result<u32, MapError> {
    let m = compute_m_for_map(pair_count * 2, false);
    let node_len = 1 + (m as usize + 1) + (pair_count * 8);

    let addr = buffer.len() as u32;
    let tag = (m << 4) | 0x0F;
    buffer.push(tag);
    encode_node_len(buffer, node_len as u32, m);

    // Stream pairs, replacing value at update_index
    for i in 0..pair_count {
        let (old_key_addr, old_value_addr) = map_leaf_pair(buffer, old_addr, i)
            .ok_or(MapError::InvalidNode { address: old_addr })?;

        if i == update_index {
            buffer.extend_from_slice(&key_addr.to_le_bytes());
            buffer.extend_from_slice(&new_value_addr.to_le_bytes());
        } else {
            buffer.extend_from_slice(&old_key_addr.to_le_bytes());
            buffer.extend_from_slice(&old_value_addr.to_le_bytes());
        }
    }

    Ok(addr)
}

/// Stream write a map leaf with one pair inserted.
fn stream_map_leaf_insert(
    buffer: &mut Vec<u8>,
    old_addr: u32,
    old_pair_count: usize,
    insert_index: usize,
    new_key_addr: u32,
    new_value_addr: u32,
) -> Result<u32, MapError> {
    let new_pair_count = old_pair_count + 1;
    let m = compute_m_for_map(new_pair_count * 2, false);
    let node_len = 1 + (m as usize + 1) + (new_pair_count * 8);

    let addr = buffer.len() as u32;
    let tag = (m << 4) | 0x0F;
    buffer.push(tag);
    encode_node_len(buffer, node_len as u32, m);

    // Stream pairs, inserting at insert_index
    let mut old_i = 0;
    for i in 0..new_pair_count {
        if i == insert_index {
            buffer.extend_from_slice(&new_key_addr.to_le_bytes());
            buffer.extend_from_slice(&new_value_addr.to_le_bytes());
        } else {
            let (old_key_addr, old_value_addr) = map_leaf_pair(buffer, old_addr, old_i)
                .ok_or(MapError::InvalidNode { address: old_addr })?;
            buffer.extend_from_slice(&old_key_addr.to_le_bytes());
            buffer.extend_from_slice(&old_value_addr.to_le_bytes());
            old_i += 1;
        }
    }

    Ok(addr)
}

/// Split a leaf into a branch when adding a new key.
/// Uses offset-based reads to get existing pairs from the old leaf.
fn split_leaf_to_branch(
    buffer: &mut Vec<u8>,
    old_addr: u32,
    pair_count: usize,
    new_key_addr: u32,
    new_value_addr: u32,
    new_hash: u32,
    depth: u8,
) -> Result<u32, MapError> {
    // Extract existing key data (we need to collect because we'll be mutating buffer)
    // Note: This still allocates, but only for the split operation which is rare
    let mut existing_key_data: Vec<(u32, u32, String, u32)> = Vec::with_capacity(pair_count);
    for i in 0..pair_count {
        let (key_addr, value_addr) = map_leaf_pair(buffer, old_addr, i)
            .ok_or(MapError::InvalidNode { address: old_addr })?;

        let key_bytes = buffer.get(key_addr as usize..).ok_or(MapError::InvalidNode {
            address: key_addr,
        })?;
        let key_node = ValueNode::new(key_bytes).ok_or(MapError::InvalidNode {
            address: key_addr,
        })?;

        if let ValueNode::Txt(s) = key_node {
            let hash = xxh32(s.as_bytes(), 0);
            existing_key_data.push((key_addr, value_addr, s.to_string(), hash));
        }
    }

    // Start with a new branch containing just the new key
    let new_slot = slot(new_hash, depth);
    let new_leaf = encode_map_leaf(buffer, &[(new_key_addr, new_value_addr)]);

    let mut bitmap = 1u32 << new_slot;
    let mut entries = vec![new_leaf];

    // Add each existing pair
    for (existing_key_addr, existing_value_addr, existing_key_str, existing_hash) in existing_key_data
    {
        let existing_slot = slot(existing_hash, depth);

        if bit_set(bitmap, existing_slot) {
            // Slot already occupied: recurse
            let i = child_index(bitmap, existing_slot);
            let child_addr = entries[i];
            let new_child = map_set_depth(
                buffer,
                child_addr,
                existing_key_addr,
                existing_value_addr,
                &existing_key_str,
                existing_hash,
                depth + 1,
            )?;
            entries[i] = new_child;
        } else {
            // New slot: add leaf
            let leaf = encode_map_leaf(buffer, &[(existing_key_addr, existing_value_addr)]);
            let i = child_index(bitmap, existing_slot);
            entries.insert(i, leaf);
            bitmap |= 1 << existing_slot;
        }
    }

    Ok(encode_map_branch(buffer, bitmap, &entries))
}

/// Delete key from map HAMT, returning new root address.
///
/// If the key doesn't exist, returns the unchanged root address.
///
/// # Arguments
/// * `buffer` - Mutable buffer to append new nodes to
/// * `node_addr` - Current root map node address
/// * `key_str` - The key to delete
///
/// # Returns
/// New root address after COW update.
pub fn map_del(buffer: &mut Vec<u8>, node_addr: u32, key_str: &str) -> Result<u32, MapError> {
    let hash = xxh32(key_str.as_bytes(), 0);
    match map_del_depth(buffer, node_addr, key_str, hash, 0)? {
        DeleteResult::Updated(new_addr) => Ok(new_addr),
        DeleteResult::Empty => {
            // Root became empty: return an empty leaf
            Ok(encode_map_leaf(buffer, &[]))
        }
        DeleteResult::NotFound => Ok(node_addr),
    }
}

/// Result of a delete operation.
enum DeleteResult {
    Updated(u32), // New node address
    Empty,        // Node is now empty
    NotFound,     // Key wasn't found
}

/// Internal recursive delete with depth tracking.
fn map_del_depth(
    buffer: &mut Vec<u8>,
    node_addr: u32,
    key_str: &str,
    hash: u32,
    depth: u8,
) -> Result<DeleteResult, MapError> {
    let node_type =
        map_node_type(buffer, node_addr).ok_or(MapError::InvalidNode { address: node_addr })?;

    match node_type {
        MapNodeType::Branch => map_del_branch(buffer, node_addr, key_str, hash, depth),
        MapNodeType::Leaf => map_del_leaf(buffer, node_addr, key_str),
    }
}

/// Delete from a branch node using offset-based reads and streaming encoding.
fn map_del_branch(
    buffer: &mut Vec<u8>,
    old_addr: u32,
    key_str: &str,
    hash: u32,
    depth: u8,
) -> Result<DeleteResult, MapError> {
    let s = slot(hash, depth);

    let old_bitmap =
        map_branch_bitmap(buffer, old_addr).ok_or(MapError::InvalidNode { address: old_addr })?;
    let old_count = map_branch_entry_count(buffer, old_addr)
        .ok_or(MapError::InvalidNode { address: old_addr })?;

    if !bit_set(old_bitmap, s) {
        return Ok(DeleteResult::NotFound);
    }

    let i = child_index(old_bitmap, s);
    let child_addr =
        map_branch_entry(buffer, old_addr, i).ok_or(MapError::InvalidNode { address: old_addr })?;

    match map_del_depth(buffer, child_addr, key_str, hash, depth + 1)? {
        DeleteResult::Updated(new_child_addr) => {
            // Stream write new branch with updated entry
            let new_addr =
                stream_map_branch_update(buffer, old_addr, old_bitmap, old_count, i, new_child_addr)?;
            Ok(DeleteResult::Updated(new_addr))
        }
        DeleteResult::Empty => {
            // Remove this slot
            let new_bitmap = old_bitmap & !(1 << s);

            if old_count == 1 {
                // Branch is now empty
                Ok(DeleteResult::Empty)
            } else {
                // Stream write new branch with entry removed
                let new_addr =
                    stream_map_branch_delete(buffer, old_addr, new_bitmap, old_count, i)?;
                Ok(DeleteResult::Updated(new_addr))
            }
        }
        DeleteResult::NotFound => Ok(DeleteResult::NotFound),
    }
}

/// Stream write a map branch with one entry removed.
fn stream_map_branch_delete(
    buffer: &mut Vec<u8>,
    old_addr: u32,
    new_bitmap: u32,
    old_count: usize,
    delete_index: usize,
) -> Result<u32, MapError> {
    let new_count = old_count - 1;
    let m = compute_m_for_map(new_count, true);
    let node_len = 1 + (m as usize + 1) + 4 + (new_count * 4);

    let addr = buffer.len() as u32;
    let tag = (m << 4) | 0x07;
    buffer.push(tag);
    encode_node_len(buffer, node_len as u32, m);
    buffer.extend_from_slice(&new_bitmap.to_le_bytes());

    // Stream entries, skipping delete_index
    let mut old_i = 0;
    for _ in 0..new_count {
        if old_i == delete_index {
            old_i += 1;
        }
        let entry = map_branch_entry(buffer, old_addr, old_i)
            .ok_or(MapError::InvalidNode { address: old_addr })?;
        buffer.extend_from_slice(&entry.to_le_bytes());
        old_i += 1;
    }

    Ok(addr)
}

/// Delete from a leaf node using offset-based reads and streaming encoding.
fn map_del_leaf(
    buffer: &mut Vec<u8>,
    old_addr: u32,
    key_str: &str,
) -> Result<DeleteResult, MapError> {
    let pair_count =
        map_leaf_pair_count(buffer, old_addr).ok_or(MapError::InvalidNode { address: old_addr })?;

    // Find the key by reading pairs one at a time
    for i in 0..pair_count {
        let (existing_key_addr, _existing_value_addr) = map_leaf_pair(buffer, old_addr, i)
            .ok_or(MapError::InvalidNode { address: old_addr })?;

        let key_bytes = buffer
            .get(existing_key_addr as usize..)
            .ok_or(MapError::InvalidNode {
                address: existing_key_addr,
            })?;
        let key_node = ValueNode::new(key_bytes).ok_or(MapError::InvalidNode {
            address: existing_key_addr,
        })?;

        if let ValueNode::Txt(existing_key) = key_node
            && existing_key == key_str
        {
            // Found it: remove
            if pair_count == 1 {
                return Ok(DeleteResult::Empty);
            } else {
                let new_addr = stream_map_leaf_delete(buffer, old_addr, pair_count, i)?;
                return Ok(DeleteResult::Updated(new_addr));
            }
        }
    }

    Ok(DeleteResult::NotFound)
}

/// Stream write a map leaf with one pair removed.
fn stream_map_leaf_delete(
    buffer: &mut Vec<u8>,
    old_addr: u32,
    old_pair_count: usize,
    delete_index: usize,
) -> Result<u32, MapError> {
    let new_pair_count = old_pair_count - 1;
    let m = compute_m_for_map(new_pair_count * 2, false);
    let node_len = 1 + (m as usize + 1) + (new_pair_count * 8);

    let addr = buffer.len() as u32;
    let tag = (m << 4) | 0x0F;
    buffer.push(tag);
    encode_node_len(buffer, node_len as u32, m);

    // Stream pairs, skipping delete_index
    let mut old_i = 0;
    for _ in 0..new_pair_count {
        if old_i == delete_index {
            old_i += 1;
        }
        let (old_key_addr, old_value_addr) = map_leaf_pair(buffer, old_addr, old_i)
            .ok_or(MapError::InvalidNode { address: old_addr })?;
        buffer.extend_from_slice(&old_key_addr.to_le_bytes());
        buffer.extend_from_slice(&old_value_addr.to_le_bytes());
        old_i += 1;
    }

    Ok(addr)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_slot() {
        // depth=0, hash=0x12345678 -> slot = 0x8
        assert_eq!(slot(0x12345678, 0), 0x8);
        // depth=1, hash=0x12345678 -> slot = 0x7
        assert_eq!(slot(0x12345678, 1), 0x7);
        // depth=7, hash=0x12345678 -> slot = 0x1
        assert_eq!(slot(0x12345678, 7), 0x1);
    }

    #[test]
    fn test_child_index() {
        // bitmap with only slot 0 set, querying slot 0
        assert_eq!(child_index(0b1, 0), 0);
        // bitmap with slots 0,2,4 set, querying slot 4
        assert_eq!(child_index(0b10101, 4), 2);
        // bitmap with slots 0,6,11 set (0x0841), querying slot 6
        assert_eq!(child_index(0x0841, 6), 1);
        // bitmap with slots 0,6,11 set (0x0841), querying slot 11
        assert_eq!(child_index(0x0841, 11), 2);
    }

    #[test]
    fn test_xxh32_keys() {
        // Test known hashes for map keys
        // "value" -> used in spec example
        let hash_value = xxh32(b"value", 0);
        let slot_value = slot(hash_value, 0);
        assert_eq!(slot_value, 0); // slot 0

        // "path" -> used in spec example
        let hash_path = xxh32(b"path", 0);
        let slot_path = slot(hash_path, 0);
        assert_eq!(slot_path, 6); // slot 6

        // "op" -> used in spec example
        let hash_op = xxh32(b"op", 0);
        let slot_op = slot(hash_op, 0);
        assert_eq!(slot_op, 11); // slot 11
    }

    #[test]
    fn test_map_get_single_key() {
        // Build a simple single-entry map: {"hi": 42}
        // First, compute hash of "hi" to know which slot
        let hash_hi = xxh32(b"hi", 0);
        let _slot_hi = slot(hash_hi, 0);

        // Structure:
        //   0x00: txt "hi"
        //   0x03: i64 value 42
        //   0x0C: map leaf with key @0x00, value @0x03
        //   footer
        let buffer = vec![
            // 0x00: txt "hi" (packed, len=2)
            0x2C, 0x68, 0x69,
            // 0x03: i64 value 42
            0x02, 0x2A, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            // 0x0C: map leaf
            0x0F, // tag: map, leaf, M=0
            0x0A, // node_len=10
            0x00, 0x00, 0x00, 0x00, // key addr -> @0x00
            0x03, 0x00, 0x00, 0x00, // value addr -> @0x03
            // footer
            0x0C, 0x00, 0x00, 0x00, // root_node_offset
            0x00, 0x00, 0x00, 0x00, // prev_root
            b'T', b'R', b'O', b'N',
        ];

        let result = map_get(&buffer, 0x0C, "hi");
        assert_eq!(result, Some(ValueNode::I64(42)));

        // Non-existent key
        let result = map_get(&buffer, 0x0C, "bye");
        assert_eq!(result, None);
    }

    #[test]
    fn test_map_get_with_branch() {
        // Build a map with branch: {"value": 1, "path": 2, "op": 3}
        // These keys hash to slots 0, 6, 11 respectively at depth 0
        // So we need a branch node pointing to three leaf nodes

        let buffer = vec![
            // 0x00: txt "value" (packed, len=5)
            0x5C, 0x76, 0x61, 0x6C, 0x75, 0x65,
            // 0x06: i64 value 1
            0x02, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            // 0x0F: map leaf {"value": 1}
            0x0F, 0x0A,
            0x00, 0x00, 0x00, 0x00, // key -> @0x00
            0x06, 0x00, 0x00, 0x00, // value -> @0x06

            // 0x19: txt "path" (packed, len=4)
            0x4C, 0x70, 0x61, 0x74, 0x68,
            // 0x1E: i64 value 2
            0x02, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            // 0x27: map leaf {"path": 2}
            0x0F, 0x0A,
            0x19, 0x00, 0x00, 0x00, // key -> @0x19
            0x1E, 0x00, 0x00, 0x00, // value -> @0x1E

            // 0x31: txt "op" (packed, len=2)
            0x2C, 0x6F, 0x70,
            // 0x34: i64 value 3
            0x02, 0x03, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            // 0x3D: map leaf {"op": 3}
            0x0F, 0x0A,
            0x31, 0x00, 0x00, 0x00, // key -> @0x31
            0x34, 0x00, 0x00, 0x00, // value -> @0x34

            // 0x47: map branch (slots 0, 6, 11 = bitmap 0x0841)
            0x07, // tag: map, branch, M=0
            0x12, // node_len=18
            0x41, 0x08, 0x00, 0x00, // bitmap = 0x0841
            0x0F, 0x00, 0x00, 0x00, // slot[0] -> @0x0F (leaf "value")
            0x27, 0x00, 0x00, 0x00, // slot[6] -> @0x27 (leaf "path")
            0x3D, 0x00, 0x00, 0x00, // slot[11] -> @0x3D (leaf "op")

            // footer
            0x47, 0x00, 0x00, 0x00, // root_node_offset
            0x00, 0x00, 0x00, 0x00, // prev_root
            b'T', b'R', b'O', b'N',
        ];

        assert_eq!(map_get(&buffer, 0x47, "value"), Some(ValueNode::I64(1)));
        assert_eq!(map_get(&buffer, 0x47, "path"), Some(ValueNode::I64(2)));
        assert_eq!(map_get(&buffer, 0x47, "op"), Some(ValueNode::I64(3)));
        assert_eq!(map_get(&buffer, 0x47, "missing"), None);
    }

    #[test]
    fn test_map_set_new_key_in_leaf() {
        use crate::encode::encode_map_leaf;

        // Create initial map {"hi": 42}
        let mut buffer = Vec::new();
        let root_addr = encode_map_leaf(&mut buffer, &[]);
        let root_addr = map_set(&mut buffer, root_addr, "hi", Value::I64(42)).unwrap();

        // Verify initial state
        assert_eq!(map_get(&buffer, root_addr, "hi"), Some(ValueNode::I64(42)));

        // Add new key {"bye": 100}
        let new_root = map_set(&mut buffer, root_addr, "bye", Value::I64(100)).unwrap();

        // Verify both keys exist
        assert_eq!(map_get(&buffer, new_root, "hi"), Some(ValueNode::I64(42)));
        assert_eq!(map_get(&buffer, new_root, "bye"), Some(ValueNode::I64(100)));

        // Old root still works (COW)
        assert_eq!(map_get(&buffer, root_addr, "hi"), Some(ValueNode::I64(42)));
        assert_eq!(map_get(&buffer, root_addr, "bye"), None);
    }

    #[test]
    fn test_map_set_update_existing_key() {
        use crate::encode::encode_map_leaf;

        // Create initial map {"key": 1}
        let mut buffer = Vec::new();
        let root_addr = encode_map_leaf(&mut buffer, &[]);
        let root_addr = map_set(&mut buffer, root_addr, "key", Value::I64(1)).unwrap();

        // Update value to 999
        let new_root = map_set(&mut buffer, root_addr, "key", Value::I64(999)).unwrap();

        // Verify update
        assert_eq!(map_get(&buffer, new_root, "key"), Some(ValueNode::I64(999)));

        // Old root unchanged (COW)
        assert_eq!(map_get(&buffer, root_addr, "key"), Some(ValueNode::I64(1)));
    }

    #[test]
    fn test_map_del_existing_key() {
        use crate::encode::{encode_i64, encode_map_leaf, encode_txt};

        // Create initial map {"a": 1, "b": 2}
        let mut buffer = Vec::new();
        let key_a = encode_txt(&mut buffer, "a");
        let val_a = encode_i64(&mut buffer, 1);
        let key_b = encode_txt(&mut buffer, "b");
        let val_b = encode_i64(&mut buffer, 2);
        let root_addr = encode_map_leaf(&mut buffer, &[(key_a, val_a), (key_b, val_b)]);

        // Delete "a"
        let new_root = map_del(&mut buffer, root_addr, "a").unwrap();

        // Verify "a" is gone, "b" remains
        assert_eq!(map_get(&buffer, new_root, "a"), None);
        assert_eq!(map_get(&buffer, new_root, "b"), Some(ValueNode::I64(2)));

        // Old root unchanged (COW)
        assert_eq!(map_get(&buffer, root_addr, "a"), Some(ValueNode::I64(1)));
    }

    #[test]
    fn test_map_del_nonexistent_key() {
        use crate::encode::{encode_i64, encode_map_leaf, encode_txt};

        let mut buffer = Vec::new();
        let key_addr = encode_txt(&mut buffer, "key");
        let val_addr = encode_i64(&mut buffer, 1);
        let root_addr = encode_map_leaf(&mut buffer, &[(key_addr, val_addr)]);

        // Delete nonexistent key
        let new_root = map_del(&mut buffer, root_addr, "missing").unwrap();

        // Should return unchanged root
        assert_eq!(new_root, root_addr);
    }

    #[test]
    fn test_map_set_creates_branch() {
        use crate::encode::encode_map_leaf;

        // Create initial map with single key
        let mut buffer = Vec::new();
        let root_addr = encode_map_leaf(&mut buffer, &[]);
        let root_addr = map_set(&mut buffer, root_addr, "value", Value::I64(1)).unwrap(); // hashes to slot 0

        // Add key that hashes to different slot
        let new_root = map_set(&mut buffer, root_addr, "op", Value::I64(2)).unwrap(); // hashes to slot 11

        // Both keys should be accessible
        assert_eq!(map_get(&buffer, new_root, "value"), Some(ValueNode::I64(1)));
        assert_eq!(map_get(&buffer, new_root, "op"), Some(ValueNode::I64(2)));
    }
}

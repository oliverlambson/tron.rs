//! HAMT (Hash Array Mapped Trie) operations for TRON maps.
//!
//! Maps use a 16-way HAMT keyed by xxh32 of UTF-8 key bytes (seed=0).
//! Each level consumes 4 bits of the hash.

use crate::document::Document;
use crate::encode::{encode_map_branch, encode_map_leaf, encode_txt};
use crate::error::{Error, Result};
use crate::value::{MapNode, Typed, Value};
use crate::xxh32::xxh32;

/// Maximum depth of the HAMT (32-bit hash / 4 bits per level = 8 levels, 0-7).
pub const MAX_DEPTH: usize = 7;

/// Calculate slot from hash at given depth.
///
/// Each level consumes 4 bits of the hash, starting from the least significant.
#[inline]
pub fn slot(hash: u32, depth: usize) -> u32 {
    (hash >> (depth * 4)) & 0xF
}

/// Calculate child index from bitmap and slot.
///
/// The index is the count of set bits before the slot position.
#[inline]
pub fn child_index(bitmap: u32, slot: u32) -> usize {
    (bitmap & ((1 << slot) - 1)).count_ones() as usize
}

/// Check if a slot is present in the bitmap.
#[inline]
pub fn has_slot(bitmap: u32, slot: u32) -> bool {
    (bitmap >> slot) & 1 == 1
}

/// Look up a key in a map, returning the value address if found.
///
/// This is a read-only operation that does not modify the document.
pub fn map_get(data: &[u8], node_addr: u32, key: &str) -> Result<Option<u32>> {
    map_get_depth(data, node_addr, key, 0)
}

fn map_get_depth(data: &[u8], node_addr: u32, key: &str, depth: usize) -> Result<Option<u32>> {
    let node = MapNode::new(data, node_addr);
    let hash = xxh32(key.as_bytes(), 0);

    if node.is_leaf() {
        // Linear search in leaf
        for i in 0..node.entry_count() {
            let (key_addr, val_addr) = node.get_kv_addrs(i).ok_or(Error::AddressOutOfBounds {
                addr: node_addr,
                len: data.len(),
            })?;
            let key_value = Value::new(data, key_addr)?;
            if matches!(key_value.typed(), Typed::Str(k) if k == key) {
                return Ok(Some(val_addr));
            }
        }
        return Ok(None);
    }

    // Branch node
    let s = slot(hash, depth);
    let bitmap = node.bitmap().unwrap_or(0);

    if !has_slot(bitmap, s) {
        return Ok(None);
    }

    let idx = child_index(bitmap, s);
    let child_addr = node.get_child_addr(idx).ok_or(Error::AddressOutOfBounds {
        addr: node_addr,
        len: data.len(),
    })?;

    map_get_depth(data, child_addr, key, depth + 1)
}

/// Set a key-value pair in a map, returning the new root address.
///
/// This is a copy-on-write operation that appends new nodes to the document.
/// The `value_addr` should point to an already-written value.
pub fn map_set(doc: &mut Document, node_addr: u32, key: &str, value_addr: u32) -> Result<u32> {
    map_set_depth(doc, node_addr, key, value_addr, 0)
}

fn map_set_depth(
    doc: &mut Document,
    node_addr: u32,
    key: &str,
    value_addr: u32,
    depth: usize,
) -> Result<u32> {
    let hash = xxh32(key.as_bytes(), 0);

    // Read node properties before any mutation
    let (is_leaf, bitmap, entry_count) = {
        let data = doc.as_bytes();
        let node = MapNode::new(data, node_addr);
        (node.is_leaf(), node.bitmap().unwrap_or(0), node.entry_count())
    };

    if is_leaf {
        return map_set_leaf(doc, node_addr, key, value_addr, hash, depth);
    }

    // Branch node
    let s = slot(hash, depth);

    if !has_slot(bitmap, s) {
        // Collect existing children before mutation
        let children_before: Vec<u32> = {
            let data = doc.as_bytes();
            let node = MapNode::new(data, node_addr);
            (0..entry_count)
                .filter_map(|i| node.get_child_addr(i))
                .collect()
        };

        // Insert new leaf at this slot
        let key_addr = doc.append_bytes(&encode_txt(key));
        let new_leaf = encode_map_leaf(&[(key_addr, value_addr)]);
        let leaf_addr = doc.append_bytes(&new_leaf);

        // Rebuild branch with new child
        let new_bitmap = bitmap | (1 << s);
        let insert_idx = child_index(new_bitmap, s);

        let mut children = children_before;
        children.insert(insert_idx, leaf_addr);

        let new_branch = encode_map_branch(new_bitmap, &children);
        return Ok(doc.append_bytes(&new_branch));
    }

    // Slot exists - recurse into child
    let idx = child_index(bitmap, s);
    let child_addr = {
        let data = doc.as_bytes();
        MapNode::new(data, node_addr)
            .get_child_addr(idx)
            .ok_or(Error::AddressOutOfBounds {
                addr: node_addr,
                len: data.len(),
            })?
    };
    let new_child_addr = map_set_depth(doc, child_addr, key, value_addr, depth + 1)?;

    // Rebuild branch with updated child
    let mut children: Vec<u32> = {
        let data = doc.as_bytes();
        let node = MapNode::new(data, node_addr);
        (0..node.entry_count())
            .filter_map(|i| node.get_child_addr(i))
            .collect()
    };
    children[idx] = new_child_addr;

    let new_branch = encode_map_branch(bitmap, &children);
    Ok(doc.append_bytes(&new_branch))
}

fn map_set_leaf(
    doc: &mut Document,
    node_addr: u32,
    key: &str,
    value_addr: u32,
    hash: u32,
    depth: usize,
) -> Result<u32> {
    let data = doc.as_bytes();
    let node = MapNode::new(data, node_addr);

    // Collect existing entries and check if key exists
    let mut entries: Vec<(u32, u32, String)> = Vec::new();
    let mut key_found = false;

    for i in 0..node.entry_count() {
        let (key_addr, val_addr) = node.get_kv_addrs(i).ok_or(Error::AddressOutOfBounds {
            addr: node_addr,
            len: data.len(),
        })?;
        let existing_key = match Value::new(data, key_addr)?.typed() {
            Typed::Str(s) => s.to_string(),
            _ => return Err(Error::InvalidUtf8),
        };

        if existing_key == key {
            // Replace value
            entries.push((key_addr, value_addr, existing_key));
            key_found = true;
        } else {
            entries.push((key_addr, val_addr, existing_key));
        }
    }

    if key_found {
        // Key replaced - encode new leaf
        let kv_addrs: Vec<(u32, u32)> = entries.iter().map(|(k, v, _)| (*k, *v)).collect();
        let new_leaf = encode_map_leaf(&kv_addrs);
        return Ok(doc.append_bytes(&new_leaf));
    }

    // Key not found - need to add it
    if depth >= MAX_DEPTH {
        // At max depth, add to collision bucket
        let key_addr = doc.append_bytes(&encode_txt(key));
        entries.push((key_addr, value_addr, key.to_string()));
        // Sort by key bytes for canonical order
        entries.sort_by(|a, b| a.2.as_bytes().cmp(b.2.as_bytes()));
        let kv_addrs: Vec<(u32, u32)> = entries.iter().map(|(k, v, _)| (*k, *v)).collect();
        let new_leaf = encode_map_leaf(&kv_addrs);
        return Ok(doc.append_bytes(&new_leaf));
    }

    // Single entry leaf and new key has different hash path - need to split
    if entries.len() == 1 {
        let (existing_key_addr, existing_val_addr, existing_key_str) = &entries[0];
        let existing_hash = xxh32(existing_key_str.as_bytes(), 0);

        // Check if hashes diverge at this depth
        let existing_slot = slot(existing_hash, depth);
        let new_slot = slot(hash, depth);

        if existing_slot == new_slot {
            // Same slot - need to go deeper
            // Create a child leaf with existing entry, then recursively set new key
            let child_leaf = encode_map_leaf(&[(*existing_key_addr, *existing_val_addr)]);
            let child_addr = doc.append_bytes(&child_leaf);

            // Recursively add the new key
            let new_child_addr = map_set_depth(doc, child_addr, key, value_addr, depth + 1)?;

            // Create branch pointing to child
            let bitmap = 1u32 << new_slot;
            let branch = encode_map_branch(bitmap, &[new_child_addr]);
            return Ok(doc.append_bytes(&branch));
        } else {
            // Different slots - create branch with two children
            let new_key_addr = doc.append_bytes(&encode_txt(key));

            // Create leaves for both
            let existing_leaf = encode_map_leaf(&[(*existing_key_addr, *existing_val_addr)]);
            let existing_leaf_addr = doc.append_bytes(&existing_leaf);

            let new_leaf = encode_map_leaf(&[(new_key_addr, value_addr)]);
            let new_leaf_addr = doc.append_bytes(&new_leaf);

            // Create branch
            let bitmap = (1u32 << existing_slot) | (1u32 << new_slot);
            let children = if existing_slot < new_slot {
                vec![existing_leaf_addr, new_leaf_addr]
            } else {
                vec![new_leaf_addr, existing_leaf_addr]
            };
            let branch = encode_map_branch(bitmap, &children);
            return Ok(doc.append_bytes(&branch));
        }
    }

    // Multiple entries (collision bucket at max depth) - just add
    let key_addr = doc.append_bytes(&encode_txt(key));
    entries.push((key_addr, value_addr, key.to_string()));
    entries.sort_by(|a, b| a.2.as_bytes().cmp(b.2.as_bytes()));
    let kv_addrs: Vec<(u32, u32)> = entries.iter().map(|(k, v, _)| (*k, *v)).collect();
    let new_leaf = encode_map_leaf(&kv_addrs);
    Ok(doc.append_bytes(&new_leaf))
}

/// Delete a key from a map, returning the new root address.
///
/// Returns `Ok(None)` if the map becomes empty after deletion.
pub fn map_del(doc: &mut Document, node_addr: u32, key: &str) -> Result<Option<u32>> {
    map_del_depth(doc, node_addr, key, 0)
}

fn map_del_depth(
    doc: &mut Document,
    node_addr: u32,
    key: &str,
    depth: usize,
) -> Result<Option<u32>> {
    let data = doc.as_bytes();
    let node = MapNode::new(data, node_addr);
    let hash = xxh32(key.as_bytes(), 0);

    if node.is_leaf() {
        // Find and remove key from leaf
        let mut entries: Vec<(u32, u32)> = Vec::new();
        let mut found = false;

        for i in 0..node.entry_count() {
            let (key_addr, val_addr) = node.get_kv_addrs(i).ok_or(Error::AddressOutOfBounds {
                addr: node_addr,
                len: data.len(),
            })?;
            let existing_key = match Value::new(data, key_addr)?.typed() {
                Typed::Str(s) => s,
                _ => return Err(Error::InvalidUtf8),
            };

            if existing_key == key {
                found = true;
            } else {
                entries.push((key_addr, val_addr));
            }
        }

        if !found {
            // Key not found - return unchanged
            return Ok(Some(node_addr));
        }

        if entries.is_empty() {
            // Leaf is now empty
            return Ok(None);
        }

        // Create new leaf without the deleted key
        let new_leaf = encode_map_leaf(&entries);
        return Ok(Some(doc.append_bytes(&new_leaf)));
    }

    // Branch node
    let s = slot(hash, depth);
    let bitmap = node.bitmap().unwrap_or(0);

    if !has_slot(bitmap, s) {
        // Key not found
        return Ok(Some(node_addr));
    }

    let idx = child_index(bitmap, s);
    let child_addr = node.get_child_addr(idx).ok_or(Error::AddressOutOfBounds {
        addr: node_addr,
        len: data.len(),
    })?;

    let new_child = map_del_depth(doc, child_addr, key, depth + 1)?;

    let data = doc.as_bytes();
    let node = MapNode::new(data, node_addr);

    match new_child {
        None => {
            // Child became empty - remove slot from branch
            let new_bitmap = bitmap & !(1 << s);

            if new_bitmap == 0 {
                // Branch is now empty
                return Ok(None);
            }

            // Collect remaining children
            let mut children: Vec<u32> = Vec::new();
            for i in 0..16u32 {
                if has_slot(new_bitmap, i) {
                    let old_idx = child_index(bitmap, i);
                    children.push(node.get_child_addr(old_idx).unwrap());
                }
            }

            let new_branch = encode_map_branch(new_bitmap, &children);
            Ok(Some(doc.append_bytes(&new_branch)))
        }
        Some(new_child_addr) if new_child_addr == child_addr => {
            // Child unchanged
            Ok(Some(node_addr))
        }
        Some(new_child_addr) => {
            // Rebuild branch with updated child
            let mut children: Vec<u32> = (0..node.entry_count())
                .filter_map(|i| node.get_child_addr(i))
                .collect();
            children[idx] = new_child_addr;

            let new_branch = encode_map_branch(bitmap, &children);
            Ok(Some(doc.append_bytes(&new_branch)))
        }
    }
}

/// Right-biased structural merge of two maps.
///
/// Returns the address of the merged map root. When the same key exists in
/// both maps, the value from `node_b_addr` wins.
pub fn map_merge(doc: &mut Document, node_a_addr: u32, node_b_addr: u32) -> Result<u32> {
    map_merge_depth(doc, node_a_addr, node_b_addr, 0)
}

fn map_merge_depth(
    doc: &mut Document,
    node_a_addr: u32,
    node_b_addr: u32,
    depth: usize,
) -> Result<u32> {
    let data = doc.as_bytes();
    let node_b = MapNode::new(data, node_b_addr);

    if node_b.is_leaf() {
        // B is a leaf - apply each entry to A
        let mut result_addr = node_a_addr;
        for i in 0..node_b.entry_count() {
            let data = doc.as_bytes();
            let node_b = MapNode::new(data, node_b_addr);
            let (key_addr, val_addr) = node_b.get_kv_addrs(i).ok_or(Error::AddressOutOfBounds {
                addr: node_b_addr,
                len: data.len(),
            })?;
            let key = match Value::new(data, key_addr)?.typed() {
                Typed::Str(s) => s.to_string(),
                _ => return Err(Error::InvalidUtf8),
            };
            result_addr = map_set_depth(doc, result_addr, &key, val_addr, depth)?;
        }
        return Ok(result_addr);
    }

    let data = doc.as_bytes();
    let node_a = MapNode::new(data, node_a_addr);

    if node_a.is_leaf() {
        // A is a leaf, B is a branch - clone B and add missing keys from A
        let mut result_addr = node_b_addr;

        // Check each key in A
        for i in 0..node_a.entry_count() {
            let data = doc.as_bytes();
            let node_a = MapNode::new(data, node_a_addr);
            let (key_addr, val_addr) = node_a.get_kv_addrs(i).ok_or(Error::AddressOutOfBounds {
                addr: node_a_addr,
                len: data.len(),
            })?;
            let key = match Value::new(data, key_addr)?.typed() {
                Typed::Str(s) => s.to_string(),
                _ => return Err(Error::InvalidUtf8),
            };

            // Only add if not in B
            if map_get(doc.as_bytes(), result_addr, &key)?.is_none() {
                result_addr = map_set_depth(doc, result_addr, &key, val_addr, depth)?;
            }
        }
        return Ok(result_addr);
    }

    // Both are branches - merge slot by slot
    let bitmap_a = node_a.bitmap().unwrap_or(0);
    let bitmap_b = node_b.bitmap().unwrap_or(0);
    let combined_bitmap = bitmap_a | bitmap_b;

    let mut children: Vec<u32> = Vec::new();
    let mut all_reused = true;

    for s in 0..16u32 {
        if !has_slot(combined_bitmap, s) {
            continue;
        }

        let has_a = has_slot(bitmap_a, s);
        let has_b = has_slot(bitmap_b, s);

        let child_addr = if has_a && has_b {
            // Both have this slot - merge recursively
            let idx_a = child_index(bitmap_a, s);
            let idx_b = child_index(bitmap_b, s);

            let data = doc.as_bytes();
            let child_a = MapNode::new(data, node_a_addr).get_child_addr(idx_a).unwrap();
            let child_b = MapNode::new(data, node_b_addr).get_child_addr(idx_b).unwrap();

            let merged = map_merge_depth(doc, child_a, child_b, depth + 1)?;
            if merged != child_a {
                all_reused = false;
            }
            merged
        } else if has_a {
            // Only A has this slot
            let idx_a = child_index(bitmap_a, s);
            let data = doc.as_bytes();
            MapNode::new(data, node_a_addr).get_child_addr(idx_a).unwrap()
        } else {
            // Only B has this slot
            let idx_b = child_index(bitmap_b, s);
            let data = doc.as_bytes();
            all_reused = false;
            MapNode::new(data, node_b_addr).get_child_addr(idx_b).unwrap()
        };

        children.push(child_addr);
    }

    if all_reused && combined_bitmap == bitmap_a {
        // All children reused from A and bitmap unchanged
        return Ok(node_a_addr);
    }

    let new_branch = encode_map_branch(combined_bitmap, &children);
    Ok(doc.append_bytes(&new_branch))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::encode::{encode_i64, encode_map_leaf};

    fn make_map_doc_with_entries(entries: &[(&str, i64)]) -> Document<'static> {
        let mut doc = Document::from_bytes(&encode_map_leaf(&[]));

        for (key, value) in entries {
            let val_bytes = encode_i64(*value);
            let val_addr = doc.append(&val_bytes);
            let root = doc.root_addr();
            let new_root = map_set(&mut doc, root, key, val_addr).unwrap();
            doc.set_root(new_root);
        }

        doc
    }

    #[test]
    fn test_map_get_empty() {
        let doc = Document::from_bytes(&encode_map_leaf(&[]));
        let result = map_get(doc.as_bytes(), doc.root_addr(), "foo").unwrap();
        assert_eq!(result, None);
    }

    #[test]
    fn test_map_set_and_get() {
        let mut doc = Document::from_bytes(&encode_map_leaf(&[]));

        // Set a value
        let val_bytes = encode_i64(42);
        let val_addr = doc.append(&val_bytes);
        let root = doc.root_addr();
        let new_root = map_set(&mut doc, root, "foo", val_addr).unwrap();
        doc.set_root(new_root);

        // Get it back
        let result = map_get(doc.as_bytes(), doc.root_addr(), "foo").unwrap();
        assert!(result.is_some());
        let value = Value::new(doc.as_bytes(), result.unwrap()).unwrap();
        assert!(matches!(value.typed(), Typed::I64(42)));
    }

    #[test]
    fn test_map_set_multiple() {
        let doc = make_map_doc_with_entries(&[("a", 1), ("b", 2), ("c", 3)]);

        // Verify all entries
        for (key, expected) in [("a", 1i64), ("b", 2), ("c", 3)] {
            let result = map_get(doc.as_bytes(), doc.root_addr(), key).unwrap();
            assert!(result.is_some(), "key {} not found", key);
            let value = Value::new(doc.as_bytes(), result.unwrap()).unwrap();
            assert!(matches!(value.typed(), Typed::I64(n) if n == expected));
        }
    }

    #[test]
    fn test_map_set_replace() {
        let mut doc = make_map_doc_with_entries(&[("foo", 1)]);

        // Replace value
        let val_bytes = encode_i64(999);
        let val_addr = doc.append(&val_bytes);
        let root = doc.root_addr();
        let new_root = map_set(&mut doc, root, "foo", val_addr).unwrap();
        doc.set_root(new_root);

        let result = map_get(doc.as_bytes(), doc.root_addr(), "foo").unwrap();
        let value = Value::new(doc.as_bytes(), result.unwrap()).unwrap();
        assert!(matches!(value.typed(), Typed::I64(999)));
    }

    #[test]
    fn test_map_del() {
        let mut doc = make_map_doc_with_entries(&[("a", 1), ("b", 2)]);

        // Delete "a"
        let root = doc.root_addr();
        let new_root = map_del(&mut doc, root, "a").unwrap();
        assert!(new_root.is_some());
        doc.set_root(new_root.unwrap());

        // Verify "a" is gone
        let result = map_get(doc.as_bytes(), doc.root_addr(), "a").unwrap();
        assert!(result.is_none());

        // Verify "b" still exists
        let result = map_get(doc.as_bytes(), doc.root_addr(), "b").unwrap();
        assert!(result.is_some());
    }

    #[test]
    fn test_map_del_nonexistent() {
        let mut doc = make_map_doc_with_entries(&[("a", 1)]);
        let old_root = doc.root_addr();

        // Delete nonexistent key
        let new_root = map_del(&mut doc, old_root, "nonexistent").unwrap();
        assert_eq!(new_root, Some(old_root)); // Unchanged
    }

    #[test]
    fn test_map_collision_handling() {
        // "a" and "v" collide at depth 0 (both have slot 6)
        // xxh32("a") = 0x550d7456, slot = 6
        // xxh32("v") = 0x4b146e46, slot = 6
        let doc = make_map_doc_with_entries(&[("a", 1), ("v", 2)]);

        // Both should be retrievable
        let result_a = map_get(doc.as_bytes(), doc.root_addr(), "a").unwrap();
        assert!(result_a.is_some());
        let value_a = Value::new(doc.as_bytes(), result_a.unwrap()).unwrap();
        assert!(matches!(value_a.typed(), Typed::I64(1)));

        let result_v = map_get(doc.as_bytes(), doc.root_addr(), "v").unwrap();
        assert!(result_v.is_some());
        let value_v = Value::new(doc.as_bytes(), result_v.unwrap()).unwrap();
        assert!(matches!(value_v.typed(), Typed::I64(2)));
    }

    #[test]
    fn test_slot_calculation() {
        // xxh32("a") = 0x550d7456
        let hash = xxh32(b"a", 0);
        assert_eq!(slot(hash, 0), 6); // 0x6
        assert_eq!(slot(hash, 1), 5); // 0x5
    }
}

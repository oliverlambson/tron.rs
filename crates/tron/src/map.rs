//! HAMT (Hash Array Mapped Trie) operations for TRON maps.
//!
//! Maps use a 16-way HAMT keyed by xxh32 of UTF-8 key bytes (seed=0).
//! Each level consumes 4 bits of the hash.

use crate::document::Document;
use crate::encode::{encode_map_branch, encode_map_leaf, encode_txt};
use crate::error::{Error, Result};
use crate::value::{MapNode, TypedValue, Value};
use crate::xxh32::xxh32;

/// Maximum depth of the HAMT (32-bit hash / 4 bits per level = 8 levels, 0-7).
pub const MAX_DEPTH: usize = 7;

/// Calculate slot from hash at given depth.
///
/// Each level consumes 4 bits of the hash, starting from the least significant.
#[inline]
#[must_use]
pub fn slot(hash: u32, depth: usize) -> u32 {
    (hash >> (depth * 4)) & 0xF
}

/// Calculate child index from bitmap and slot.
///
/// The index is the count of set bits before the slot position.
#[inline]
#[must_use]
pub fn child_index(bitmap: u32, slot: u32) -> usize {
    (bitmap & ((1 << slot) - 1)).count_ones() as usize
}

/// Check if a slot is present in the bitmap.
#[inline]
#[must_use]
pub fn has_slot(bitmap: u32, slot: u32) -> bool {
    (bitmap >> slot) & 1 == 1
}

/// Look up a key in a map, returning the value address if found.
///
/// This is a read-only operation that does not modify the document.
///
/// # Errors
///
/// Returns `Error::AddressOutOfBounds` if an address in the tree is invalid.
pub fn map_get(data: &[u8], node_addr: u32, key: &str) -> Result<Option<u32>> {
    map_get_depth(data, node_addr, key, 0)
}

fn map_get_depth(data: &[u8], node_addr: u32, key: &str, depth: usize) -> Result<Option<u32>> {
    let hash = xxh32(key.as_bytes(), 0);

    match MapNode::new(data, node_addr) {
        MapNode::Leaf(leaf) => {
            // Linear search in leaf
            for i in 0..leaf.entry_count() {
                let (key_addr, val_addr) =
                    leaf.get_kv_addrs(i).ok_or(Error::AddressOutOfBounds {
                        addr: node_addr,
                        len: data.len(),
                    })?;
                let key_value = Value::new(data, key_addr)?;
                if matches!(key_value.typed(), Ok(TypedValue::Str(k)) if k == key) {
                    return Ok(Some(val_addr));
                }
            }
            Ok(None)
        }
        MapNode::Branch(branch) => {
            let s = slot(hash, depth);
            let bitmap = branch.bitmap();

            if !has_slot(bitmap, s) {
                return Ok(None);
            }

            let idx = child_index(bitmap, s);
            let child_addr = branch
                .get_child_addr(idx)
                .ok_or(Error::AddressOutOfBounds {
                    addr: node_addr,
                    len: data.len(),
                })?;

            map_get_depth(data, child_addr, key, depth + 1)
        }
    }
}

/// Set a key-value pair in a map, returning the new root address.
///
/// This is a copy-on-write operation that appends new nodes to the document.
/// The `value_addr` should point to an already-written value.
///
/// # Errors
///
/// Returns an error if address resolution fails during traversal.
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
    let branch_info: Option<(u32, usize, Vec<u32>)> = {
        let data = doc.as_bytes();
        match MapNode::new(data, node_addr) {
            MapNode::Leaf(_) => None,
            MapNode::Branch(branch) => {
                let bitmap = branch.bitmap();
                let children: Vec<u32> = branch.child_addrs().collect();
                Some((bitmap, children.len(), children))
            }
        }
    };

    let Some((bitmap, _entry_count, children_before)) = branch_info else {
        return map_set_leaf(doc, node_addr, key, value_addr, hash, depth);
    };

    // Branch node
    let s = slot(hash, depth);

    if !has_slot(bitmap, s) {
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
    let child_addr = children_before[idx];
    let new_child_addr = map_set_depth(doc, child_addr, key, value_addr, depth + 1)?;

    // Rebuild branch with updated child
    let mut children = children_before;
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
    let leaf = match MapNode::new(data, node_addr) {
        MapNode::Leaf(l) => l,
        MapNode::Branch(_) => unreachable!("map_set_leaf called on branch"),
    };

    // Collect existing entries and check if key exists
    let mut entries: Vec<(u32, u32, String)> = Vec::new();
    let mut key_found = false;

    for i in 0..leaf.entry_count() {
        let (key_addr, val_addr) = leaf.get_kv_addrs(i).ok_or(Error::AddressOutOfBounds {
            addr: node_addr,
            len: data.len(),
        })?;
        let existing_key = match Value::new(data, key_addr)?.typed()? {
            TypedValue::Str(s) => s.to_string(),
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
        }

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
///
/// # Errors
///
/// Returns an error if address resolution fails during traversal.
pub fn map_del(doc: &mut Document, node_addr: u32, key: &str) -> Result<Option<u32>> {
    map_del_depth(doc, node_addr, key, 0)
}

enum DelNodeInfo {
    Leaf(Vec<(u32, u32, String)>),
    Branch { bitmap: u32, children: Vec<u32> },
}

fn map_del_depth(
    doc: &mut Document,
    node_addr: u32,
    key: &str,
    depth: usize,
) -> Result<Option<u32>> {
    let hash = xxh32(key.as_bytes(), 0);

    let node_info = {
        let data = doc.as_bytes();
        match MapNode::new(data, node_addr) {
            MapNode::Leaf(leaf) => {
                let mut entries = Vec::new();
                for i in 0..leaf.entry_count() {
                    let (key_addr, val_addr) =
                        leaf.get_kv_addrs(i).ok_or(Error::AddressOutOfBounds {
                            addr: node_addr,
                            len: data.len(),
                        })?;
                    let existing_key = match Value::new(data, key_addr)?.typed()? {
                        TypedValue::Str(s) => s.to_string(),
                        _ => return Err(Error::InvalidUtf8),
                    };
                    entries.push((key_addr, val_addr, existing_key));
                }
                DelNodeInfo::Leaf(entries)
            }
            MapNode::Branch(branch) => DelNodeInfo::Branch {
                bitmap: branch.bitmap(),
                children: branch.child_addrs().collect(),
            },
        }
    };

    match node_info {
        DelNodeInfo::Leaf(entries) => {
            let mut new_entries: Vec<(u32, u32)> = Vec::new();
            let mut found = false;

            for (key_addr, val_addr, existing_key) in entries {
                if existing_key == key {
                    found = true;
                } else {
                    new_entries.push((key_addr, val_addr));
                }
            }

            if !found {
                return Ok(Some(node_addr));
            }

            if new_entries.is_empty() {
                return Ok(None);
            }

            let new_leaf = encode_map_leaf(&new_entries);
            Ok(Some(doc.append_bytes(&new_leaf)))
        }
        DelNodeInfo::Branch { bitmap, children } => {
            let s = slot(hash, depth);

            if !has_slot(bitmap, s) {
                return Ok(Some(node_addr));
            }

            let idx = child_index(bitmap, s);
            let child_addr = children[idx];

            let new_child = map_del_depth(doc, child_addr, key, depth + 1)?;

            match new_child {
                None => {
                    let new_bitmap = bitmap & !(1 << s);

                    if new_bitmap == 0 {
                        return Ok(None);
                    }

                    let mut new_children: Vec<u32> = Vec::new();
                    for i in 0..16u32 {
                        if has_slot(new_bitmap, i) {
                            let old_idx = child_index(bitmap, i);
                            new_children.push(children[old_idx]);
                        }
                    }

                    let new_branch = encode_map_branch(new_bitmap, &new_children);
                    Ok(Some(doc.append_bytes(&new_branch)))
                }
                Some(new_child_addr) if new_child_addr == child_addr => Ok(Some(node_addr)),
                Some(new_child_addr) => {
                    let mut new_children = children;
                    new_children[idx] = new_child_addr;

                    let new_branch = encode_map_branch(bitmap, &new_children);
                    Ok(Some(doc.append_bytes(&new_branch)))
                }
            }
        }
    }
}

/// Right-biased structural merge of two maps.
///
/// Returns the address of the merged map root. When the same key exists in
/// both maps, the value from `node_b_addr` wins.
///
/// # Errors
///
/// Returns an error if address resolution fails during traversal.
#[allow(clippy::similar_names)]
pub fn map_merge(doc: &mut Document, node_a_addr: u32, node_b_addr: u32) -> Result<u32> {
    map_merge_depth(doc, node_a_addr, node_b_addr, 0)
}

#[allow(clippy::similar_names, clippy::too_many_lines)]
fn map_merge_depth(
    doc: &mut Document,
    node_a_addr: u32,
    node_b_addr: u32,
    depth: usize,
) -> Result<u32> {
    // Collect B's entries if it's a leaf
    let b_leaf_entries: Option<Vec<(u32, u32, String)>> = {
        let data = doc.as_bytes();
        match MapNode::new(data, node_b_addr) {
            MapNode::Leaf(leaf) => {
                let mut entries = Vec::new();
                for i in 0..leaf.entry_count() {
                    let (key_addr, val_addr) =
                        leaf.get_kv_addrs(i).ok_or(Error::AddressOutOfBounds {
                            addr: node_b_addr,
                            len: data.len(),
                        })?;
                    let key = match Value::new(data, key_addr)?.typed()? {
                        TypedValue::Str(s) => s.to_string(),
                        _ => return Err(Error::InvalidUtf8),
                    };
                    entries.push((key_addr, val_addr, key));
                }
                Some(entries)
            }
            MapNode::Branch(_) => None,
        }
    };

    if let Some(entries) = b_leaf_entries {
        // B is a leaf - apply each entry to A
        let mut result_addr = node_a_addr;
        for (_key_addr, val_addr, key) in entries {
            result_addr = map_set_depth(doc, result_addr, &key, val_addr, depth)?;
        }
        return Ok(result_addr);
    }

    // B is a branch, check if A is a leaf
    let a_leaf_entries: Option<Vec<(u32, u32, String)>> = {
        let data = doc.as_bytes();
        match MapNode::new(data, node_a_addr) {
            MapNode::Leaf(leaf) => {
                let mut entries = Vec::new();
                for i in 0..leaf.entry_count() {
                    let (key_addr, val_addr) =
                        leaf.get_kv_addrs(i).ok_or(Error::AddressOutOfBounds {
                            addr: node_a_addr,
                            len: data.len(),
                        })?;
                    let key = match Value::new(data, key_addr)?.typed()? {
                        TypedValue::Str(s) => s.to_string(),
                        _ => return Err(Error::InvalidUtf8),
                    };
                    entries.push((key_addr, val_addr, key));
                }
                Some(entries)
            }
            MapNode::Branch(_) => None,
        }
    };

    if let Some(entries) = a_leaf_entries {
        // A is a leaf, B is a branch - clone B and add missing keys from A
        let mut result_addr = node_b_addr;
        for (_key_addr, val_addr, key) in entries {
            if map_get(doc.as_bytes(), result_addr, &key)?.is_none() {
                result_addr = map_set_depth(doc, result_addr, &key, val_addr, depth)?;
            }
        }
        return Ok(result_addr);
    }

    // Both are branches - get their info
    let (bitmap_a, children_a) = {
        let data = doc.as_bytes();
        match MapNode::new(data, node_a_addr) {
            MapNode::Branch(b) => (b.bitmap(), b.child_addrs().collect::<Vec<_>>()),
            MapNode::Leaf(_) => unreachable!(),
        }
    };
    let (bitmap_b, children_b) = {
        let data = doc.as_bytes();
        match MapNode::new(data, node_b_addr) {
            MapNode::Branch(b) => (b.bitmap(), b.child_addrs().collect::<Vec<_>>()),
            MapNode::Leaf(_) => unreachable!(),
        }
    };

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
            let idx_a = child_index(bitmap_a, s);
            let idx_b = child_index(bitmap_b, s);
            let child_a = children_a[idx_a];
            let child_b = children_b[idx_b];

            let merged = map_merge_depth(doc, child_a, child_b, depth + 1)?;
            if merged != child_a {
                all_reused = false;
            }
            merged
        } else if has_a {
            let idx_a = child_index(bitmap_a, s);
            children_a[idx_a]
        } else {
            let idx_b = child_index(bitmap_b, s);
            all_reused = false;
            children_b[idx_b]
        };

        children.push(child_addr);
    }

    if all_reused && combined_bitmap == bitmap_a {
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
        assert!(matches!(value.typed(), Ok(TypedValue::I64(42))));
    }

    #[test]
    fn test_map_set_multiple() {
        let doc = make_map_doc_with_entries(&[("a", 1), ("b", 2), ("c", 3)]);

        // Verify all entries
        for (key, expected) in [("a", 1i64), ("b", 2), ("c", 3)] {
            let result = map_get(doc.as_bytes(), doc.root_addr(), key).unwrap();
            assert!(result.is_some(), "key {key} not found");
            let value = Value::new(doc.as_bytes(), result.unwrap()).unwrap();
            assert!(matches!(value.typed(), Ok(TypedValue::I64(n)) if n == expected));
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
        assert!(matches!(value.typed(), Ok(TypedValue::I64(999))));
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
        assert!(matches!(value_a.typed(), Ok(TypedValue::I64(1))));

        let result_v = map_get(doc.as_bytes(), doc.root_addr(), "v").unwrap();
        assert!(result_v.is_some());
        let value_v = Value::new(doc.as_bytes(), result_v.unwrap()).unwrap();
        assert!(matches!(value_v.typed(), Ok(TypedValue::I64(2))));
    }

    #[test]
    fn test_slot_calculation() {
        // xxh32("a") = 0x550d7456
        let hash = xxh32(b"a", 0);
        assert_eq!(slot(hash, 0), 6); // 0x6
        assert_eq!(slot(hash, 1), 5); // 0x5
    }
}

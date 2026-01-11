//! Vector trie operations for TRON arrays.
//!
//! Arrays use a 16-way vector trie indexed by element position.
//! Each level consumes 4 bits of the index.

use std::cell::RefCell;

use crate::document::Document;
use crate::encode::{encode_arr_branch, encode_arr_leaf};
use crate::error::{Error, Result};
use crate::value::ArrNode;

/// Calculate slot from index at given shift.
#[inline]
#[must_use]
pub fn slot(index: u32, shift: u8) -> u32 {
    (index >> shift) & 0xF
}

/// Calculate child index from bitmap and slot.
#[inline]
#[must_use]
pub fn child_index(bitmap: u16, slot: u32) -> usize {
    (bitmap & ((1 << slot) - 1)).count_ones() as usize
}

/// Check if a slot is present in the bitmap.
#[inline]
#[must_use]
pub fn has_slot(bitmap: u16, slot: u32) -> bool {
    (bitmap >> slot) & 1 == 1
}

/// Calculate the minimum shift required to cover a given length.
///
/// Returns 0 for lengths <= 16, 4 for <= 256, etc.
#[must_use]
pub fn required_shift(length: u32) -> u8 {
    if length == 0 {
        return 0;
    }
    let max_index = length - 1;
    let mut shift = 0u8;
    while (max_index >> shift) > 0xF {
        shift += 4;
    }
    shift
}

/// Look up an element in an array by index.
///
/// Returns `Ok(Some(addr))` if found, `Ok(None)` if index is in a sparse region,
/// or `Err` if index is out of bounds.
///
/// # Errors
///
/// Returns `Error::IndexOutOfBounds` if the index exceeds the array length.
/// Returns `Error::AddressOutOfBounds` if an address in the tree is invalid.
pub fn arr_get(data: &[u8], node_addr: u32, index: u32) -> Result<Option<u32>> {
    let node = ArrNode::new(data, node_addr);

    // Check bounds if root
    if node.is_root()
        && let Some(length) = node.length()
        && index >= length
    {
        return Err(Error::IndexOutOfBounds { index, length });
    }

    arr_get_internal(data, node_addr, index)
}

fn arr_get_internal(data: &[u8], node_addr: u32, index: u32) -> Result<Option<u32>> {
    let node = ArrNode::new(data, node_addr);
    let shift = node.shift();
    let s = slot(index, shift);
    let bitmap = node.bitmap();

    if !has_slot(bitmap, s) {
        return Ok(None); // Sparse array - index not present
    }

    let idx = child_index(bitmap, s);
    let entry_addr = node.get_entry_addr(idx).ok_or(Error::AddressOutOfBounds {
        addr: node_addr,
        len: data.len(),
    })?;

    if node.is_leaf() {
        // Entry is a value address
        Ok(Some(entry_addr))
    } else {
        // Entry is a child node - recurse
        arr_get_internal(data, entry_addr, index)
    }
}

/// Set an element in an array, returning the new root address.
///
/// The index must be within the current array length. Use `arr_append` to add
/// elements beyond the current length.
///
/// # Errors
///
/// Returns `Error::IndexOutOfBounds` if the index exceeds the array length.
/// Returns `Error::AddressOutOfBounds` if an address in the tree is invalid.
pub fn arr_set(doc: &mut Document, root_addr: u32, index: u32, value_addr: u32) -> Result<u32> {
    let data = doc.as_bytes();
    let root = ArrNode::new(data, root_addr);

    // Check bounds
    let length = root.length().ok_or(Error::AddressOutOfBounds {
        addr: root_addr,
        len: data.len(),
    })?;

    if index >= length {
        return Err(Error::IndexOutOfBounds { index, length });
    }

    arr_set_internal(doc, root_addr, index, value_addr, true, Some(length))
}

fn arr_set_internal(
    doc: &mut Document,
    node_addr: u32,
    index: u32,
    value_addr: u32,
    is_root: bool,
    length: Option<u32>,
) -> Result<u32> {
    let data = doc.as_bytes();
    let node = ArrNode::new(data, node_addr);

    let shift = node.shift();
    let s = slot(index, shift);
    let bitmap = node.bitmap();

    if node.is_leaf() {
        // Set value in leaf
        let new_bitmap = bitmap | (1 << s);
        let insert_idx = child_index(new_bitmap, s);
        let old_count = node.entry_count();

        let mut entries: Vec<u32> = (0..old_count)
            .filter_map(|i| node.get_entry_addr(i))
            .collect();

        if has_slot(bitmap, s) {
            // Replace existing
            let idx = child_index(bitmap, s);
            entries[idx] = value_addr;
        } else {
            // Insert new
            entries.insert(insert_idx, value_addr);
        }

        let new_leaf = encode_arr_leaf(is_root, shift, new_bitmap, length, &entries);
        return Ok(doc.append_bytes(&new_leaf));
    }

    // Branch node
    if !has_slot(bitmap, s) {
        // Need to create new child path down to leaf
        let child_addr = create_arr_path(doc, shift.saturating_sub(4), index, value_addr)?;

        let new_bitmap = bitmap | (1 << s);
        let insert_idx = child_index(new_bitmap, s);

        let data = doc.as_bytes();
        let node = ArrNode::new(data, node_addr);
        let mut children: Vec<u32> = (0..node.entry_count())
            .filter_map(|i| node.get_entry_addr(i))
            .collect();
        children.insert(insert_idx, child_addr);

        let new_branch = encode_arr_branch(is_root, shift, new_bitmap, length, &children);
        return Ok(doc.append_bytes(&new_branch));
    }

    // Slot exists - recurse
    let idx = child_index(bitmap, s);
    let child_addr = node.get_entry_addr(idx).ok_or(Error::AddressOutOfBounds {
        addr: node_addr,
        len: doc.len(),
    })?;

    let new_child_addr = arr_set_internal(doc, child_addr, index, value_addr, false, None)?;

    // Rebuild branch with updated child
    let data = doc.as_bytes();
    let node = ArrNode::new(data, node_addr);
    let mut children: Vec<u32> = (0..node.entry_count())
        .filter_map(|i| node.get_entry_addr(i))
        .collect();
    children[idx] = new_child_addr;

    let new_branch = encode_arr_branch(is_root, shift, bitmap, length, &children);
    Ok(doc.append_bytes(&new_branch))
}

/// Create a path of nodes down to a leaf for a new index.
fn create_arr_path(doc: &mut Document, shift: u8, index: u32, value_addr: u32) -> Result<u32> {
    if shift == 0 {
        // Create leaf with single entry
        let s = slot(index, 0);
        let bitmap = 1u16 << s;
        let leaf = encode_arr_leaf(false, 0, bitmap, None, &[value_addr]);
        return Ok(doc.append_bytes(&leaf));
    }

    // Create child path first
    let child_addr = create_arr_path(doc, shift - 4, index, value_addr)?;

    // Create branch pointing to child
    let s = slot(index, shift);
    let bitmap = 1u16 << s;
    let branch = encode_arr_branch(false, shift, bitmap, None, &[child_addr]);
    Ok(doc.append_bytes(&branch))
}

/// Append a value to an array, returning the new root address.
///
/// # Errors
///
/// Returns `Error::AddressOutOfBounds` if an address in the tree is invalid.
pub fn arr_append(doc: &mut Document, root_addr: u32, value_addr: u32) -> Result<u32> {
    let data = doc.as_bytes();
    let root = ArrNode::new(data, root_addr);

    let length = root.length().unwrap_or(0);
    let new_length = length + 1;
    let new_index = length;

    // Check if we need to grow the root
    let current_shift = root.shift();
    let required = required_shift(new_length);

    if required > current_shift {
        // Need to grow: create new root with current root as child at slot 0
        // and new element in a new path at the appropriate slot

        // Read old root properties before mutation
        let (old_shift, old_bitmap, old_entries, old_is_leaf) = {
            let data = doc.as_bytes();
            let old_root = ArrNode::new(data, root_addr);
            let entries: Vec<u32> = (0..old_root.entry_count())
                .filter_map(|i| old_root.get_entry_addr(i))
                .collect();
            (
                old_root.shift(),
                old_root.bitmap(),
                entries,
                old_root.is_leaf(),
            )
        };

        // Create path for new element
        let new_path = create_arr_path(doc, required - 4, new_index, value_addr)?;

        let old_slot = 0u32; // Old root covers indices starting at 0
        let new_slot = slot(new_index, required);

        let bitmap = (1u16 << old_slot) | (1u16 << new_slot);

        // Demote old root to a child (remove length, set R=1)
        let demoted_child = if old_is_leaf {
            let child = encode_arr_leaf(false, old_shift, old_bitmap, None, &old_entries);
            doc.append_bytes(&child)
        } else {
            let child = encode_arr_branch(false, old_shift, old_bitmap, None, &old_entries);
            doc.append_bytes(&child)
        };

        let children = if old_slot < new_slot {
            vec![demoted_child, new_path]
        } else {
            vec![new_path, demoted_child]
        };

        let new_root = encode_arr_branch(true, required, bitmap, Some(new_length), &children);
        return Ok(doc.append_bytes(&new_root));
    }

    // Set at new index and update length
    arr_append_internal(doc, root_addr, new_index, value_addr, true, new_length)
}

fn arr_append_internal(
    doc: &mut Document,
    node_addr: u32,
    index: u32,
    value_addr: u32,
    is_root: bool,
    new_length: u32,
) -> Result<u32> {
    let data = doc.as_bytes();
    let node = ArrNode::new(data, node_addr);

    let shift = node.shift();
    let s = slot(index, shift);
    let bitmap = node.bitmap();

    let length = if is_root { Some(new_length) } else { None };

    if node.is_leaf() {
        // Add to leaf
        let new_bitmap = bitmap | (1 << s);
        let insert_idx = child_index(new_bitmap, s);

        let mut entries: Vec<u32> = (0..node.entry_count())
            .filter_map(|i| node.get_entry_addr(i))
            .collect();
        entries.insert(insert_idx, value_addr);

        let new_leaf = encode_arr_leaf(is_root, shift, new_bitmap, length, &entries);
        return Ok(doc.append_bytes(&new_leaf));
    }

    // Branch node
    if !has_slot(bitmap, s) {
        // Create new child path
        let child_addr = create_arr_path(doc, shift.saturating_sub(4), index, value_addr)?;

        let new_bitmap = bitmap | (1 << s);
        let insert_idx = child_index(new_bitmap, s);

        let data = doc.as_bytes();
        let node = ArrNode::new(data, node_addr);
        let mut children: Vec<u32> = (0..node.entry_count())
            .filter_map(|i| node.get_entry_addr(i))
            .collect();
        children.insert(insert_idx, child_addr);

        let new_branch = encode_arr_branch(is_root, shift, new_bitmap, length, &children);
        return Ok(doc.append_bytes(&new_branch));
    }

    // Recurse into existing child
    let idx = child_index(bitmap, s);
    let child_addr = node.get_entry_addr(idx).ok_or(Error::AddressOutOfBounds {
        addr: node_addr,
        len: doc.len(),
    })?;

    let new_child_addr =
        arr_append_internal(doc, child_addr, index, value_addr, false, new_length)?;

    let data = doc.as_bytes();
    let node = ArrNode::new(data, node_addr);
    let mut children: Vec<u32> = (0..node.entry_count())
        .filter_map(|i| node.get_entry_addr(i))
        .collect();
    children[idx] = new_child_addr;

    let new_branch = encode_arr_branch(is_root, shift, bitmap, length, &children);
    Ok(doc.append_bytes(&new_branch))
}

/// Cached array accessor with spine cache for efficient random access.
///
/// This caches the addresses of leaf chunks to avoid re-traversing the trie
/// for repeated lookups.
pub struct CachedArray<'a> {
    data: &'a [u8],
    root_addr: u32,
    length: u32,
    shift: u8,
    /// Spine cache: maps chunk index to leaf address.
    /// Populated lazily during traversal.
    spine_cache: RefCell<Vec<Option<u32>>>,
}

impl<'a> CachedArray<'a> {
    /// Create a new cached array accessor.
    ///
    /// # Errors
    ///
    /// This function currently does not fail, but returns `Result` for API consistency.
    pub fn new(data: &'a [u8], root_addr: u32) -> Result<Self> {
        let root = ArrNode::new(data, root_addr);
        let length = root.length().unwrap_or(0);
        let shift = root.shift();

        // Calculate number of leaf chunks (each leaf covers 16 indices at shift=0)
        let chunk_count = if length == 0 {
            0
        } else {
            ((length - 1) / 16 + 1) as usize
        };

        Ok(Self {
            data,
            root_addr,
            length,
            shift,
            spine_cache: RefCell::new(vec![None; chunk_count]),
        })
    }

    /// Get the array length.
    #[inline]
    #[must_use]
    pub fn len(&self) -> u32 {
        self.length
    }

    /// Check if the array is empty.
    #[inline]
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.length == 0
    }

    /// Get an element by index.
    ///
    /// # Errors
    ///
    /// Returns `Error::IndexOutOfBounds` if the index exceeds the array length.
    /// Returns `Error::KeyNotFound` if the traversal fails (should not happen for valid arrays).
    pub fn get(&self, index: u32) -> Result<Option<u32>> {
        if index >= self.length {
            return Err(Error::IndexOutOfBounds {
                index,
                length: self.length,
            });
        }

        // For small arrays (shift=0), go directly to root
        if self.shift == 0 {
            return arr_get_internal(self.data, self.root_addr, index);
        }

        let chunk_index = (index / 16) as usize;

        // Check cache
        {
            let cache = self.spine_cache.borrow();
            if let Some(Some(leaf_addr)) = cache.get(chunk_index) {
                return Ok(self.get_from_leaf(*leaf_addr, index));
            }
        }

        // Cache miss - find the leaf
        let leaf_addr = self.find_leaf(index)?;

        // Update cache
        {
            let mut cache = self.spine_cache.borrow_mut();
            if chunk_index < cache.len() {
                cache[chunk_index] = Some(leaf_addr);
            }
        }

        Ok(self.get_from_leaf(leaf_addr, index))
    }

    fn find_leaf(&self, index: u32) -> Result<u32> {
        let mut node_addr = self.root_addr;
        let mut node = ArrNode::new(self.data, node_addr);

        while node.is_branch() {
            let s = slot(index, node.shift());
            let bitmap = node.bitmap();

            if !has_slot(bitmap, s) {
                return Err(Error::KeyNotFound);
            }

            let idx = child_index(bitmap, s);
            node_addr = node.get_entry_addr(idx).ok_or(Error::AddressOutOfBounds {
                addr: node_addr,
                len: self.data.len(),
            })?;
            node = ArrNode::new(self.data, node_addr);
        }

        Ok(node_addr)
    }

    fn get_from_leaf(&self, leaf_addr: u32, index: u32) -> Option<u32> {
        let leaf = ArrNode::new(self.data, leaf_addr);
        let s = slot(index, 0); // Leaf always has shift=0
        let bitmap = leaf.bitmap();

        if !has_slot(bitmap, s) {
            return None;
        }

        let idx = child_index(bitmap, s);
        leaf.get_entry_addr(idx)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::encode::{encode_arr_leaf, encode_i64};
    use crate::value::TypedValue;

    fn empty_arr_doc() -> Document<'static> {
        Document::from_bytes(&encode_arr_leaf(true, 0, 0, Some(0), &[]))
    }

    fn make_arr_doc(values: &[i64]) -> Document<'static> {
        let mut doc = empty_arr_doc();

        for value in values {
            let val_bytes = encode_i64(*value);
            let val_addr = doc.append(&val_bytes);
            let root = doc.root_addr();
            let new_root = arr_append(&mut doc, root, val_addr).unwrap();
            doc.set_root(new_root);
        }

        doc
    }

    #[test]
    fn test_required_shift() {
        assert_eq!(required_shift(0), 0);
        assert_eq!(required_shift(1), 0);
        assert_eq!(required_shift(16), 0);
        assert_eq!(required_shift(17), 4);
        assert_eq!(required_shift(256), 4);
        assert_eq!(required_shift(257), 8);
    }

    #[test]
    fn test_arr_get_empty() {
        let doc = empty_arr_doc();
        let result = arr_get(doc.as_bytes(), doc.root_addr(), 0);
        assert!(matches!(result, Err(Error::IndexOutOfBounds { .. })));
    }

    #[test]
    fn test_arr_append_and_get() {
        let mut doc = empty_arr_doc();

        // Append a value
        let val_bytes = encode_i64(42);
        let val_addr = doc.append(&val_bytes);
        let root = doc.root_addr();
        let new_root = arr_append(&mut doc, root, val_addr).unwrap();
        doc.set_root(new_root);

        // Get it back
        let result = arr_get(doc.as_bytes(), doc.root_addr(), 0).unwrap();
        assert!(result.is_some());

        // Check length
        let root = ArrNode::new(doc.as_bytes(), doc.root_addr());
        assert_eq!(root.length(), Some(1));
    }

    #[test]
    fn test_arr_append_multiple() {
        let doc = make_arr_doc(&[10, 20, 30]);

        let root = ArrNode::new(doc.as_bytes(), doc.root_addr());
        assert_eq!(root.length(), Some(3));

        // Verify all elements
        for (i, expected) in [10i64, 20, 30].iter().enumerate() {
            let result = arr_get(doc.as_bytes(), doc.root_addr(), i as u32).unwrap();
            assert!(result.is_some(), "index {i} not found");
            let value = crate::value::Value::new(doc.as_bytes(), result.unwrap()).unwrap();
            assert!(matches!(value.typed(), Ok(TypedValue::I64(n)) if n == *expected));
        }
    }

    #[test]
    fn test_arr_set() {
        let mut doc = make_arr_doc(&[1, 2, 3]);

        // Set index 1 to 999
        let val_bytes = encode_i64(999);
        let val_addr = doc.append(&val_bytes);
        let root = doc.root_addr();
        let new_root = arr_set(&mut doc, root, 1, val_addr).unwrap();
        doc.set_root(new_root);

        // Verify
        let result = arr_get(doc.as_bytes(), doc.root_addr(), 1).unwrap();
        let value = crate::value::Value::new(doc.as_bytes(), result.unwrap()).unwrap();
        assert!(matches!(value.typed(), Ok(TypedValue::I64(999))));

        // Other elements unchanged
        let result = arr_get(doc.as_bytes(), doc.root_addr(), 0).unwrap();
        let value = crate::value::Value::new(doc.as_bytes(), result.unwrap()).unwrap();
        assert!(matches!(value.typed(), Ok(TypedValue::I64(1))));
    }

    #[test]
    fn test_arr_multi_level() {
        // Create array with 17 elements (forces multi-level trie)
        let values: Vec<i64> = (0..17).collect();
        let doc = make_arr_doc(&values);

        let root = ArrNode::new(doc.as_bytes(), doc.root_addr());
        assert_eq!(root.length(), Some(17));
        assert_eq!(root.shift(), 4); // Multi-level

        // Verify all elements
        for (i, expected) in values.iter().enumerate() {
            let result = arr_get(doc.as_bytes(), doc.root_addr(), i as u32).unwrap();
            assert!(result.is_some(), "index {i} not found");
            let value = crate::value::Value::new(doc.as_bytes(), result.unwrap()).unwrap();
            assert!(
                matches!(value.typed(), Ok(TypedValue::I64(n)) if n == *expected),
                "index {i} wrong value"
            );
        }
    }

    #[test]
    fn test_cached_array() {
        let values: Vec<i64> = (0..20).collect();
        let doc = make_arr_doc(&values);

        let cached = CachedArray::new(doc.as_bytes(), doc.root_addr()).unwrap();
        assert_eq!(cached.len(), 20);

        // Access elements (first access populates cache)
        for i in 0..20 {
            let result = cached.get(i).unwrap();
            assert!(result.is_some());
        }

        // Access again (should use cache)
        for i in 0..20 {
            let result = cached.get(i).unwrap();
            assert!(result.is_some());
        }
    }
}

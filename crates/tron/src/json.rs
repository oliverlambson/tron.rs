//! JSON serialization and deserialization for TRON documents.
//!
//! This module provides bidirectional conversion between JSON strings and
//! TRON documents according to the mapping defined in the TRON specification.
//!
//! # Example
//!
//! ```
//! use tron::json::{from_json, to_json};
//!
//! // Parse JSON to TRON
//! let doc = from_json(r#"{"name": "alice", "age": 30}"#).unwrap();
//!
//! // Convert back to JSON
//! let json = to_json(&doc).unwrap();
//! ```
//!
//! # TRON to JSON Mapping
//!
//! | TRON  | JSON                                     |
//! |-------|------------------------------------------|
//! | `nil` | null                                     |
//! | `bit` | true/false                               |
//! | `i64` | integer (fits i64)                       |
//! | `f64` | other number                             |
//! | `bin` | string with `b64:` prefix (valid base64) |
//! | `txt` | other string                             |
//! | `arr` | array                                    |
//! | `map` | object                                   |

use base64::Engine;
use serde_json::Value as JsonValue;

use crate::arr::{self, child_index, has_slot};
use crate::document::Document;
use crate::encode;
use crate::error::{Error, Result};
use crate::value::{ArrNode, MapNode, TypedValue, Value};

/// Parse a JSON string and create a canonical TRON Document.
///
/// The resulting document is in canonical form with no history (`prev_root` = 0).
///
/// # Errors
///
/// Returns `Error::JsonParse` if the JSON is invalid.
pub fn from_json(json: &str) -> Result<Document<'static>> {
    let json_value: JsonValue =
        serde_json::from_str(json).map_err(|e| Error::JsonParse(e.to_string()))?;

    // Build canonical document using a two-phase approach:
    // 1. Build all values into a buffer (depth-first post-order)
    // 2. Create document from the buffer with proper header/footer
    let mut builder = CanonicalBuilder::new();
    let root_addr = builder.build_value(&json_value)?;

    Ok(builder.finish(root_addr))
}

/// Builder for canonical TRON documents.
///
/// Builds values in depth-first post-order directly into a byte buffer,
/// producing canonical output without history.
struct CanonicalBuilder {
    /// Buffer for node data (header is prepended at finish)
    buffer: Vec<u8>,
}

impl CanonicalBuilder {
    fn new() -> Self {
        // Start with header
        Self {
            buffer: b"TRON".to_vec(),
        }
    }

    /// Current write position (address for next append)
    fn current_addr(&self) -> u32 {
        self.buffer.len() as u32
    }

    /// Append bytes and return the start address
    fn append(&mut self, bytes: &[u8]) -> u32 {
        let addr = self.current_addr();
        self.buffer.extend_from_slice(bytes);
        addr
    }

    /// Finish building and create the document
    fn finish(mut self, root_addr: u32) -> Document<'static> {
        // Append footer: root_addr + prev_root_addr (0 for canonical)
        self.buffer.extend_from_slice(&root_addr.to_le_bytes());
        self.buffer.extend_from_slice(&0u32.to_le_bytes());

        // Create document from assembled bytes
        Document::from_slice(&self.buffer)
            .expect("canonical builder should produce valid document")
            .into_owned()
    }

    /// Build a JSON value recursively, returning its address
    fn build_value(&mut self, value: &JsonValue) -> Result<u32> {
        match value {
            JsonValue::Null => Ok(self.append(&encode::encode_nil())),

            JsonValue::Bool(b) => Ok(self.append(&encode::encode_bool(*b))),

            JsonValue::Number(n) => {
                if let Some(i) = n.as_i64() {
                    Ok(self.append(&encode::encode_i64(i)))
                } else if let Some(f) = n.as_f64() {
                    Ok(self.append(&encode::encode_f64(f)))
                } else {
                    Ok(self.append(&encode::encode_f64(0.0)))
                }
            }

            JsonValue::String(s) => {
                if let Some(b64_payload) = s.strip_prefix("b64:")
                    && let Ok(bytes) = base64::engine::general_purpose::STANDARD.decode(b64_payload)
                {
                    return Ok(self.append(&encode::encode_bin(&bytes)));
                }
                Ok(self.append(&encode::encode_txt(s)))
            }

            JsonValue::Array(arr) => self.build_array(arr),

            JsonValue::Object(obj) => self.build_map(obj),
        }
    }

    /// Build an array using canonical HAMT structure
    fn build_array(&mut self, items: &[JsonValue]) -> Result<u32> {
        if items.is_empty() {
            // Empty array: single root leaf with no entries
            return Ok(self.append(&encode::encode_arr_leaf(true, 0, 0, Some(0), &[])));
        }

        let length = items.len() as u32;
        let shift = arr::required_shift(length);

        // Build all values first (depth-first)
        let mut value_addrs = Vec::with_capacity(items.len());
        for item in items {
            value_addrs.push(self.build_value(item)?);
        }

        // Build the trie structure
        self.build_arr_trie(true, shift, &value_addrs, 0, length)
    }

    /// Build array trie nodes recursively
    fn build_arr_trie(
        &mut self,
        is_root: bool,
        shift: u8,
        value_addrs: &[u32],
        base_index: u32,
        length: u32,
    ) -> Result<u32> {
        // Calculate which slots are needed at this level
        let mut slots_needed: Vec<(u32, Vec<u32>)> = Vec::new();

        for (i, &addr) in value_addrs.iter().enumerate() {
            let index = base_index + i as u32;
            let slot = (index >> shift) & 0xF;

            if let Some((last_slot, addrs)) = slots_needed.last_mut()
                && *last_slot == slot
            {
                addrs.push(addr);
                continue;
            }
            slots_needed.push((slot, vec![addr]));
        }

        if shift == 0 {
            // Leaf node - entries are value addresses
            let bitmap: u16 = slots_needed.iter().fold(0, |b, (s, _)| b | (1 << s));
            let entries: Vec<u32> = slots_needed.iter().map(|(_, addrs)| addrs[0]).collect();
            let len = if is_root { Some(length) } else { None };
            Ok(self.append(&encode::encode_arr_leaf(is_root, 0, bitmap, len, &entries)))
        } else {
            // Branch node - need to build children first
            let mut child_addrs = Vec::new();
            let mut bitmap: u16 = 0;

            for (slot, addrs) in &slots_needed {
                bitmap |= 1 << slot;
                let child_base = base_index + (slot << shift);
                let child_addr =
                    self.build_arr_trie(false, shift - 4, addrs, child_base, length)?;
                child_addrs.push(child_addr);
            }

            let len = if is_root { Some(length) } else { None };
            Ok(self.append(&encode::encode_arr_branch(
                is_root,
                shift,
                bitmap,
                len,
                &child_addrs,
            )))
        }
    }

    /// Build a map using canonical HAMT structure.
    ///
    /// Canonical order: process slots in ascending order, for each slot write
    /// (key, value, leaf) in that order, children before parents.
    fn build_map(&mut self, obj: &serde_json::Map<String, JsonValue>) -> Result<u32> {
        if obj.is_empty() {
            return Ok(self.append(&encode::encode_map_leaf(&[])));
        }

        // Collect entries with their hashes
        let entries: Vec<_> = obj
            .iter()
            .map(|(k, v)| (k.clone(), crate::xxh32(k.as_bytes(), 0), v.clone()))
            .collect();

        self.build_map_node(&entries, 0)
    }

    /// Build map trie node recursively with canonical ordering.
    fn build_map_node(&mut self, entries: &[(String, u32, JsonValue)], depth: u8) -> Result<u32> {
        const MAX_DEPTH: u8 = 7;

        if entries.is_empty() {
            return Ok(self.append(&encode::encode_map_leaf(&[])));
        }

        // Group entries by slot at this depth
        let mut slots: std::collections::BTreeMap<u32, Vec<(String, u32, JsonValue)>> =
            std::collections::BTreeMap::new();
        for (key, hash, value) in entries {
            let slot = (hash >> (depth * 4)) & 0xF;
            slots
                .entry(slot)
                .or_default()
                .push((key.clone(), *hash, value.clone()));
        }

        // Check if we need a branch (multiple slots occupied)
        let needs_branch =
            slots.len() > 1 || (depth < MAX_DEPTH && slots.values().any(|v| v.len() > 1));

        if !needs_branch {
            // Single slot with single entry (or at max depth for collision bucket)
            // Sort entries by key for canonical ordering
            let mut sorted_entries: Vec<_> = entries.to_vec();
            sorted_entries.sort_by(|a, b| a.0.cmp(&b.0));

            // Write key, then value, for each entry in sorted order
            let mut kv_addrs = Vec::new();
            for (key, _, value) in &sorted_entries {
                let key_addr = self.append(&encode::encode_txt(key));
                let value_addr = self.build_value(value)?;
                kv_addrs.push((key_addr, value_addr));
            }
            return Ok(self.append(&encode::encode_map_leaf(&kv_addrs)));
        }

        // Build branch with children in slot order (BTreeMap ensures ascending order)
        let mut child_addrs = Vec::new();
        let mut bitmap: u32 = 0;

        for (&slot, slot_entries) in &slots {
            bitmap |= 1 << slot;

            if slot_entries.len() == 1 {
                // Single entry in slot - write key, value, then leaf
                let (key, _, value) = &slot_entries[0];
                let key_addr = self.append(&encode::encode_txt(key));
                let value_addr = self.build_value(value)?;
                let leaf_addr = self.append(&encode::encode_map_leaf(&[(key_addr, value_addr)]));
                child_addrs.push(leaf_addr);
            } else {
                // Multiple entries (collision) - recurse to next depth
                let child_addr = self.build_map_node(slot_entries, depth + 1)?;
                child_addrs.push(child_addr);
            }
        }

        Ok(self.append(&encode::encode_map_branch(bitmap, &child_addrs)))
    }
}

/// Convert a TRON Document to a JSON string.
///
/// # Errors
///
/// Returns `Error::NonFiniteFloat` if an f64 value is NaN or Infinity.
/// Returns `Error::JsonSerialize` if JSON serialization fails.
/// Returns other errors if the document structure is invalid.
pub fn to_json(doc: &Document) -> Result<String> {
    let json_value = value_to_json(doc.as_bytes(), doc.root())?;
    serde_json::to_string(&json_value).map_err(|e| Error::JsonSerialize(e.to_string()))
}

// --- to_json helpers ---

fn value_to_json(data: &[u8], value: Value) -> Result<JsonValue> {
    match value.typed()? {
        TypedValue::Nil => Ok(JsonValue::Null),

        TypedValue::Bool(b) => Ok(JsonValue::Bool(b)),

        TypedValue::I64(n) => Ok(JsonValue::Number(n.into())),

        TypedValue::F64(f) => {
            if !f.is_finite() {
                return Err(Error::NonFiniteFloat(f));
            }
            let num = serde_json::Number::from_f64(f).ok_or(Error::NonFiniteFloat(f))?;
            Ok(JsonValue::Number(num))
        }

        TypedValue::Str(s) => Ok(JsonValue::String(s.to_string())),

        TypedValue::Bytes(bytes) => {
            let encoded = base64::engine::general_purpose::STANDARD.encode(bytes);
            Ok(JsonValue::String(format!("b64:{encoded}")))
        }

        TypedValue::Arr(arr) => arr_to_json(data, arr),

        TypedValue::Map(map_node) => map_to_json(data, map_node),
    }
}

fn arr_to_json(data: &[u8], arr: ArrNode) -> Result<JsonValue> {
    let length = arr.length().unwrap_or(0);

    if length == 0 {
        return Ok(JsonValue::Array(vec![]));
    }

    // Collect all (index, value_addr) pairs via tree traversal
    let mut index_map = vec![None; length as usize];
    collect_arr_values(data, arr, 0, &mut index_map);

    // Build dense JSON array
    let mut items = Vec::with_capacity(length as usize);
    for slot in index_map {
        match slot {
            Some(addr) => {
                let val = Value::new(data, addr)?;
                items.push(value_to_json(data, val)?);
            }
            None => {
                // Sparse array slot - use null
                items.push(JsonValue::Null);
            }
        }
    }

    Ok(JsonValue::Array(items))
}

/// Recursively collect array values via tree traversal.
/// Stores `Some(addr)` at each index in `index_map`.
fn collect_arr_values(data: &[u8], node: ArrNode, base_index: u32, index_map: &mut [Option<u32>]) {
    let shift = node.shift();
    let bitmap = node.bitmap();

    for slot in 0..16u32 {
        if has_slot(bitmap, slot) {
            let idx = child_index(bitmap, slot);
            if let Some(entry_addr) = node.get_entry_addr(idx) {
                let logical_index = base_index + (slot << shift);

                if node.is_leaf() {
                    // Store value address
                    if (logical_index as usize) < index_map.len() {
                        index_map[logical_index as usize] = Some(entry_addr);
                    }
                } else {
                    // Recurse into child node
                    let child = ArrNode::new(data, entry_addr);
                    collect_arr_values(data, child, logical_index, index_map);
                }
            }
        }
    }
}

fn map_to_json(data: &[u8], map_node: MapNode) -> Result<JsonValue> {
    let mut obj = serde_json::Map::new();
    collect_map_entries(data, map_node, &mut obj)?;
    Ok(JsonValue::Object(obj))
}

/// Recursively collect map key-value pairs via tree traversal.
fn collect_map_entries(
    data: &[u8],
    map_node: MapNode,
    obj: &mut serde_json::Map<String, JsonValue>,
) -> Result<()> {
    match map_node {
        MapNode::Leaf(leaf) => {
            for (key_addr, val_addr) in leaf.kv_pairs() {
                let key_value = Value::new(data, key_addr)?;
                let key = match key_value.typed()? {
                    TypedValue::Str(s) => s.to_string(),
                    _ => return Err(Error::InvalidUtf8), // Map keys must be strings
                };
                let val = Value::new(data, val_addr)?;
                let json_val = value_to_json(data, val)?;
                obj.insert(key, json_val);
            }
        }
        MapNode::Branch(branch) => {
            // Recursively collect from all children
            for child_addr in branch.child_addrs() {
                let child_map = MapNode::new(data, child_addr);
                collect_map_entries(data, child_map, obj)?;
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::map;

    #[test]
    fn test_from_json_null() {
        let doc = from_json("null").unwrap();
        assert!(matches!(doc.root().typed(), Ok(TypedValue::Nil)));
    }

    #[test]
    fn test_from_json_bool() {
        let doc = from_json("true").unwrap();
        assert!(matches!(doc.root().typed(), Ok(TypedValue::Bool(true))));

        let doc = from_json("false").unwrap();
        assert!(matches!(doc.root().typed(), Ok(TypedValue::Bool(false))));
    }

    #[test]
    fn test_from_json_integer() {
        let doc = from_json("42").unwrap();
        assert!(matches!(doc.root().typed(), Ok(TypedValue::I64(42))));

        // Negative
        let doc = from_json("-100").unwrap();
        assert!(matches!(doc.root().typed(), Ok(TypedValue::I64(-100))));

        // Max i64
        let doc = from_json("9223372036854775807").unwrap();
        assert!(matches!(doc.root().typed(), Ok(TypedValue::I64(i64::MAX))));
    }

    #[test]
    fn test_from_json_float() {
        let doc = from_json("1.23").unwrap();
        if let Ok(TypedValue::F64(f)) = doc.root().typed() {
            assert!((f - 1.23).abs() < 1e-10);
        } else {
            panic!("expected F64");
        }
    }

    #[test]
    fn test_from_json_string() {
        let doc = from_json(r#""hello""#).unwrap();
        assert!(matches!(doc.root().typed(), Ok(TypedValue::Str("hello"))));
    }

    #[test]
    fn test_from_json_binary() {
        // "b64:SGVsbG8=" decodes to "Hello"
        let doc = from_json(r#""b64:SGVsbG8=""#).unwrap();
        match doc.root().typed() {
            Ok(TypedValue::Bytes(b)) => assert_eq!(b, b"Hello"),
            other => panic!("expected Bytes, got {other:?}"),
        }
    }

    #[test]
    fn test_from_json_invalid_base64_is_txt() {
        // Invalid base64 after b64: should remain as txt
        let doc = from_json(r#""b64:!!!invalid!!!""#).unwrap();
        assert!(matches!(
            doc.root().typed(),
            Ok(TypedValue::Str("b64:!!!invalid!!!"))
        ));
    }

    #[test]
    fn test_from_json_array() {
        let doc = from_json("[1, 2, 3]").unwrap();
        if let Ok(TypedValue::Arr(arr)) = doc.root().typed() {
            assert_eq!(arr.length(), Some(3));
        } else {
            panic!("expected Arr");
        }
    }

    #[test]
    fn test_from_json_empty_array() {
        let doc = from_json("[]").unwrap();
        if let Ok(TypedValue::Arr(arr)) = doc.root().typed() {
            assert_eq!(arr.length(), Some(0));
        } else {
            panic!("expected Arr");
        }
    }

    #[test]
    fn test_from_json_object() {
        let doc = from_json(r#"{"a": 1, "b": 2}"#).unwrap();
        assert!(matches!(doc.root().typed(), Ok(TypedValue::Map(_))));

        // Verify we can look up keys
        let result = map::map_get(doc.as_bytes(), doc.root_addr(), "a").unwrap();
        assert!(result.is_some());
    }

    #[test]
    fn test_from_json_empty_object() {
        let doc = from_json("{}").unwrap();
        if let Ok(TypedValue::Map(map_node)) = doc.root().typed() {
            assert_eq!(map_node.entry_count(), 0);
        } else {
            panic!("expected Map");
        }
    }

    #[test]
    fn test_to_json_null() {
        let doc = Document::from_value(&encode::Nil);
        let json = to_json(&doc).unwrap();
        assert_eq!(json, "null");
    }

    #[test]
    fn test_to_json_bool() {
        let doc = Document::from_value(&true);
        assert_eq!(to_json(&doc).unwrap(), "true");

        let doc = Document::from_value(&false);
        assert_eq!(to_json(&doc).unwrap(), "false");
    }

    #[test]
    fn test_to_json_integer() {
        let doc = Document::from_value(&42i64);
        assert_eq!(to_json(&doc).unwrap(), "42");
    }

    #[test]
    fn test_to_json_float() {
        let doc = Document::from_value(&1.23f64);
        let json = to_json(&doc).unwrap();
        assert!(json.starts_with("1.23"));
    }

    #[test]
    fn test_to_json_string() {
        let doc = Document::from_value(&"hello");
        assert_eq!(to_json(&doc).unwrap(), r#""hello""#);
    }

    #[test]
    fn test_to_json_binary() {
        let doc = Document::from_value(&encode::Bin(b"Hello"));
        let json = to_json(&doc).unwrap();
        assert_eq!(json, r#""b64:SGVsbG8=""#);
    }

    #[test]
    fn test_to_json_non_finite_float_error() {
        let doc = Document::from_value(&f64::NAN);
        let result = to_json(&doc);
        assert!(matches!(result, Err(Error::NonFiniteFloat(_))));

        let doc = Document::from_value(&f64::INFINITY);
        let result = to_json(&doc);
        assert!(matches!(result, Err(Error::NonFiniteFloat(_))));
    }

    #[test]
    fn test_roundtrip_simple() {
        let original = r#"{"name":"alice","age":30}"#;
        let doc = from_json(original).unwrap();
        let result = to_json(&doc).unwrap();

        // Parse both and compare structure (order may differ)
        let orig_val: serde_json::Value = serde_json::from_str(original).unwrap();
        let result_val: serde_json::Value = serde_json::from_str(&result).unwrap();
        assert_eq!(orig_val, result_val);
    }

    #[test]
    fn test_roundtrip_nested() {
        let original = r#"{"name":"alice","scores":[10,20,30]}"#;
        let doc = from_json(original).unwrap();
        let result = to_json(&doc).unwrap();

        let orig_val: serde_json::Value = serde_json::from_str(original).unwrap();
        let result_val: serde_json::Value = serde_json::from_str(&result).unwrap();
        assert_eq!(orig_val, result_val);
    }

    #[test]
    fn test_roundtrip_array() {
        let original = r#"[1,2,3,null,"hello",true]"#;
        let doc = from_json(original).unwrap();
        let result = to_json(&doc).unwrap();

        let orig_val: serde_json::Value = serde_json::from_str(original).unwrap();
        let result_val: serde_json::Value = serde_json::from_str(&result).unwrap();
        assert_eq!(orig_val, result_val);
    }

    #[test]
    fn test_roundtrip_binary() {
        let original = r#"{"data":"b64:SGVsbG8gV29ybGQ="}"#;
        let doc = from_json(original).unwrap();
        let result = to_json(&doc).unwrap();

        let orig_val: serde_json::Value = serde_json::from_str(original).unwrap();
        let result_val: serde_json::Value = serde_json::from_str(&result).unwrap();
        assert_eq!(orig_val, result_val);
    }

    #[test]
    fn test_from_json_parse_error() {
        let result = from_json("not valid json");
        assert!(matches!(result, Err(Error::JsonParse(_))));
    }
}

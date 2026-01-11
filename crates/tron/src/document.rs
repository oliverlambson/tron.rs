//! TRON document.

use std::borrow::Cow;

use crate::value::{ArrValue, ValueNode};
use crate::{arr, footer::Footer, map};

#[derive(Debug, PartialEq)]
pub struct Tron<'a> {
    buffer: Cow<'a, [u8]>,
    root: ValueNode<'a>,
    root_addr: u32,
}
impl<'a> Tron<'a> {
    pub fn from_bytes(bytes: &'a [u8]) -> Option<Self> {
        let footer_bytes = bytes.get(bytes.len().checked_sub(12)?..)?;
        let footer = Footer::new(footer_bytes.try_into().ok()?)?;

        let root_node_bytes = bytes.get(footer.root_node_offset as usize..bytes.len() - 12)?;
        let root_node = ValueNode::new(root_node_bytes)?;

        Some(Tron {
            buffer: Cow::Borrowed(bytes),
            root: root_node,
            root_addr: footer.root_node_offset,
        })
    }

    /// Get the root node.
    pub fn root(&self) -> &ValueNode<'a> {
        &self.root
    }

    /// Get the underlying buffer.
    pub fn buffer(&self) -> &[u8] {
        &self.buffer
    }

    /// Get array element if root is an array.
    pub fn get_arr(&self, index: u32) -> Option<ValueNode<'_>> {
        match &self.root {
            ValueNode::Arr(arr) => {
                let length = match arr {
                    ArrValue::Root(root) => root.length,
                    ArrValue::Child(_) => return None, // Document root should be Root
                };
                arr::arr_get(&self.buffer, self.root_addr, index, length)
            }
            _ => None,
        }
    }

    /// Get map value if root is a map.
    pub fn get_map(&self, key: &str) -> Option<ValueNode<'_>> {
        match &self.root {
            ValueNode::Map(_) => map::map_get(&self.buffer, self.root_addr, key),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_nil_document() {
        let data = [
            0x00, // nil node at offset 0
            // footer (12 bytes)
            0x00, 0x00, 0x00, 0x00, // root_node_offset: 0
            0x00, 0x00, 0x00, 0x00, // prev_root_node_offset: 0
            b'T', b'R', b'O', b'N', // magic
        ];
        let doc = Tron::from_bytes(&data).expect("failed to parse nil document");
        assert_eq!(doc.root, ValueNode::Nil);
    }

    #[test]
    fn parse_empty_map_document() {
        let data = [
            // map leaf node at offset 0
            0x0F, // type=map; B=1=leaf; M=0
            0x02, // node_len=2
            // footer (12 bytes)
            0x00, 0x00, 0x00, 0x00, // root_node_offset: 0
            0x00, 0x00, 0x00, 0x00, // prev_root_node_offset: 0
            b'T', b'R', b'O', b'N', // magic
        ];
        let doc = Tron::from_bytes(&data).expect("failed to parse empty map document");
        assert!(
            matches!(doc.root, ValueNode::Map(_)),
            "expected Map, got {:?}",
            doc.root
        );
    }
}

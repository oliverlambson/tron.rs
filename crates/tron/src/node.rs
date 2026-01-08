use crate::value::ValueType;

#[derive(Debug, PartialEq)]
pub enum NodeKind {
    Branch,
    Leaf,
}
#[derive(Debug, PartialEq)]
pub enum KeyType {
    Arr,
    Map,
}

/// Zero-copy view over raw node header.
#[derive(Debug, PartialEq)]
pub struct NodeHeaderRef<'a> {
    bytes: &'a [u8; 8],
}
impl<'a> NodeHeaderRef<'a> {
    pub fn new(data: &'a [u8]) -> Option<Self> {
        Some(Self {
            bytes: data.get(0..8)?.try_into().ok()?,
        })
    }
    pub fn kind(&self) -> NodeKind {
        if (self.bytes[0] & 0b00000001) == 0 {
            NodeKind::Branch
        } else {
            NodeKind::Leaf
        }
    }
    pub fn key_type(&self) -> KeyType {
        if (self.bytes[0] & 0b00000010) == 0 {
            KeyType::Arr
        } else {
            KeyType::Map
        }
    }
    pub fn node_len(&self) -> Result<u32, &str> {
        // bottom two bits of header u32 are always 0 in context of node_len because it's a
        // multiple of 4, that's why they can be used for kind & type
        let bytes = [
            self.bytes[0] & 0b11111100,
            self.bytes[1],
            self.bytes[2],
            self.bytes[3],
        ];
        let value = u32::from_le_bytes(bytes);
        if value.is_multiple_of(4) {
            // always true given bitmask, drop check?
            Ok(value)
        } else {
            Err("node_len not a multiple of 4")
        }
    }
    pub fn entry_count(&self) -> u32 {
        u32::from_le_bytes(self.bytes[4..8].try_into().unwrap())
    }
}

/// Zero-copy view over raw node array leaf node.
#[derive(Debug, PartialEq)]
pub struct ArrLeafNodeRef<'a> {
    header: NodeHeaderRef<'a>,
    bytes: &'a [u8],
}
impl<'a> ArrLeafNodeRef<'a> {
    pub fn new(data: &'a [u8]) -> Option<Self> {
        if data.len() < 16 {
            return None;
        }

        let header = NodeHeaderRef::new(data)?;
        if header.kind() == NodeKind::Leaf && header.key_type() == KeyType::Arr {
            let bytes = data.get(8..)?;
            Some(Self { header, bytes })
        } else {
            None
        }
    }
    pub fn shift(&self) -> u8 {
        self.bytes[0]
    }
    pub fn bitmap(&self) -> Option<u16> {
        Some(u16::from_le_bytes(self.bytes[2..4].try_into().ok()?))
    }
    pub fn length(&self) -> Option<u32> {
        Some(u32::from_le_bytes(self.bytes[4..8].try_into().ok()?))
    }
    pub fn value_count(&self) -> usize {
        self.header.entry_count() as usize
    }

    /// Get value at index (requires parsing through previous values - O(n))
    pub fn value_at(&self, idx: usize) -> Option<ValueType<'a>> {
        if idx >= self.value_count() {
            return None;
        }
        let data = &self.bytes[8..]; // values start at offset 8 within bytes
        let mut offset = 0;
        for i in 0..=idx {
            if i == idx {
                return ValueType::new(&data[offset..]);
            }
            offset += ValueType::byte_len(&data[offset..])?;
        }
        None
    }
}

/// Zero-copy view over raw node array branch node.
#[derive(Debug, PartialEq)]
pub struct ArrBranchNodeRef<'a> {
    header: NodeHeaderRef<'a>,
    bytes: &'a [u8],
}
impl<'a> ArrBranchNodeRef<'a> {
    pub fn new(data: &'a [u8]) -> Option<Self> {
        if data.len() < 16 {
            return None;
        }

        let header = NodeHeaderRef::new(data)?;
        if header.kind() == NodeKind::Branch && header.key_type() == KeyType::Arr {
            let bytes = data.get(8..)?;
            Some(Self { header, bytes })
        } else {
            None
        }
    }
    pub fn shift(&self) -> u8 {
        self.bytes[0]
    }
    pub fn bitmap(&self) -> Option<u16> {
        Some(u16::from_le_bytes(self.bytes[2..4].try_into().ok()?))
    }
    pub fn length(&self) -> Option<u32> {
        Some(u32::from_le_bytes(self.bytes[4..8].try_into().ok()?))
    }
    pub fn child_count(&self) -> usize {
        self.header.entry_count() as usize
    }
    pub fn child_offset(&self, idx: usize) -> Option<u32> {
        if idx >= self.child_count() {
            return None;
        }
        let start = 8 + idx * 4;
        Some(u32::from_le_bytes(
            self.bytes.get(start..start + 4)?.try_into().ok()?,
        ))
    }
}

/// Zero-copy view over raw map branch node (HAMT).
#[derive(Debug, PartialEq)]
pub struct MapBranchNodeRef<'a> {
    header: NodeHeaderRef<'a>,
    bytes: &'a [u8],
}
impl<'a> MapBranchNodeRef<'a> {
    pub fn new(data: &'a [u8]) -> Option<Self> {
        if data.len() < 12 {
            return None;
        }

        let header = NodeHeaderRef::new(data)?;
        if header.kind() == NodeKind::Branch && header.key_type() == KeyType::Map {
            let bytes = data.get(8..)?;
            Some(Self { header, bytes })
        } else {
            None
        }
    }
    pub fn bitmap(&self) -> Option<u16> {
        Some(u16::from_le_bytes(self.bytes[0..2].try_into().ok()?))
    }
    pub fn child_count(&self) -> usize {
        self.header.entry_count() as usize
    }
    pub fn child_offset(&self, idx: usize) -> Option<u32> {
        if idx >= self.child_count() {
            return None;
        }
        let start = 4 + idx * 4; // offset 4 within bytes (after bitmap + reserved)
        Some(u32::from_le_bytes(
            self.bytes.get(start..start + 4)?.try_into().ok()?,
        ))
    }
}

/// Zero-copy view over raw map leaf node (HAMT).
#[derive(Debug, PartialEq)]
pub struct MapLeafNodeRef<'a> {
    header: NodeHeaderRef<'a>,
    bytes: &'a [u8],
}
impl<'a> MapLeafNodeRef<'a> {
    pub fn new(data: &'a [u8]) -> Option<Self> {
        if data.len() < 8 {
            return None;
        }

        let header = NodeHeaderRef::new(data)?;
        if header.kind() == NodeKind::Leaf && header.key_type() == KeyType::Map {
            let bytes = data.get(8..)?;
            Some(Self { header, bytes })
        } else {
            None
        }
    }

    pub fn entry_count(&self) -> usize {
        self.header.entry_count() as usize
    }

    /// Get key at index (requires parsing through previous entries - O(n))
    pub fn key_at(&self, idx: usize) -> Option<&'a str> {
        if idx >= self.entry_count() {
            return None;
        }
        let mut offset = 0;
        for i in 0..=idx {
            let key = match ValueType::new(&self.bytes[offset..])? {
                ValueType::Txt(s) => s,
                _ => return None, // keys must be txt
            };
            let key_len = ValueType::byte_len(&self.bytes[offset..])?;
            if i == idx {
                return Some(key);
            }
            offset += key_len;
            offset += ValueType::byte_len(&self.bytes[offset..])?; // skip value
        }
        None
    }

    /// Get value at index (requires parsing through previous entries - O(n))
    pub fn value_at(&self, idx: usize) -> Option<ValueType<'a>> {
        if idx >= self.entry_count() {
            return None;
        }
        let mut offset = 0;
        for i in 0..=idx {
            offset += ValueType::byte_len(&self.bytes[offset..])?; // skip key
            if i == idx {
                return ValueType::new(&self.bytes[offset..]);
            }
            offset += ValueType::byte_len(&self.bytes[offset..])?; // skip value
        }
        None
    }

    /// Get value by key (linear search - O(n))
    pub fn get(&self, key: &str) -> Option<ValueType<'a>> {
        let mut offset = 0;
        for _ in 0..self.entry_count() {
            let k = match ValueType::new(&self.bytes[offset..])? {
                ValueType::Txt(s) => s,
                _ => return None,
            };
            offset += ValueType::byte_len(&self.bytes[offset..])?;
            if k == key {
                return ValueType::new(&self.bytes[offset..]);
            }
            offset += ValueType::byte_len(&self.bytes[offset..])?;
        }
        None
    }
}

/// Calculate HAMT slot for a key at given depth.
pub fn map_slot(key: &str, depth: u8) -> u8 {
    use crate::xxh32::xxh32;
    let hash = xxh32(key.as_bytes(), 0);
    ((hash >> (depth * 4)) & 0xF) as u8
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::ValueType;

    // NodeHeaderRef
    #[test]
    fn header_branch_arr() {
        let data = [
            0x14, 0x00, 0x00, 0x00, // header: node_len=20 (0x14), branch=0, arr=0
            0x02, 0x00, 0x00, 0x00, // entry_count: 2
        ];
        let header = NodeHeaderRef::new(&data).unwrap();
        assert_eq!(header.kind(), NodeKind::Branch);
        assert_eq!(header.key_type(), KeyType::Arr);
        assert_eq!(header.node_len(), Ok(20));
        assert_eq!(header.entry_count(), 2);
    }

    #[test]
    fn header_leaf_arr() {
        let data = [
            0x15, 0x00, 0x00, 0x00, // header: node_len=20, leaf=1, arr=0
            0x03, 0x00, 0x00, 0x00, // entry_count: 3
        ];
        let header = NodeHeaderRef::new(&data).unwrap();
        assert_eq!(header.kind(), NodeKind::Leaf);
        assert_eq!(header.key_type(), KeyType::Arr);
        assert_eq!(header.node_len(), Ok(20));
        assert_eq!(header.entry_count(), 3);
    }

    #[test]
    fn header_branch_map() {
        let data = [
            0x16, 0x00, 0x00, 0x00, // header: node_len=20, branch=0, map=1
            0x01, 0x00, 0x00, 0x00, // entry_count: 1
        ];
        let header = NodeHeaderRef::new(&data).unwrap();
        assert_eq!(header.kind(), NodeKind::Branch);
        assert_eq!(header.key_type(), KeyType::Map);
        assert_eq!(header.node_len(), Ok(20));
        assert_eq!(header.entry_count(), 1);
    }

    #[test]
    fn header_leaf_map() {
        let data = [
            0x17, 0x00, 0x00, 0x00, // header: node_len=20, leaf=1, map=1
            0x04, 0x00, 0x00, 0x00, // entry_count: 4
        ];
        let header = NodeHeaderRef::new(&data).unwrap();
        assert_eq!(header.kind(), NodeKind::Leaf);
        assert_eq!(header.key_type(), KeyType::Map);
        assert_eq!(header.node_len(), Ok(20));
        assert_eq!(header.entry_count(), 4);
    }

    // ArrLeafNodeRef
    #[test]
    fn arr_leaf_with_values() {
        let data = [
            0x15, 0x00, 0x00, 0x00, // header: node_len=20, leaf=1, arr=0
            0x02, 0x00, 0x00, 0x00, // entry_count: 2
            0x00, // shift: 0
            0x00, // reserved: 0
            0x03, 0x00, // bitmap: 0x0003 (slots 0,1)
            0x02, 0x00, 0x00, 0x00, // length: 2
            0x00, // value 0: nil
            0x00, // value 1: nil
            0x00, 0x00, // padding to 4-byte boundary
        ];
        let node = ArrLeafNodeRef::new(&data).unwrap();
        assert_eq!(node.shift(), 0);
        assert_eq!(node.bitmap(), Some(0x0003));
        assert_eq!(node.length(), Some(2));
        assert_eq!(node.value_count(), 2);
        assert_eq!(node.value_at(0), Some(ValueType::Nil));
        assert_eq!(node.value_at(1), Some(ValueType::Nil));
        assert_eq!(node.value_at(2), None);
    }

    #[test]
    fn arr_leaf_with_nested_arr() {
        let data = [
            // Root node at offset 0x00: arr leaf containing 2 nested arrs
            0x15, 0x00, 0x00, 0x00, // header: node_len=20, leaf=1, arr=0
            0x02, 0x00, 0x00, 0x00, // entry_count: 2
            0x00, // shift: 0
            0x00, // reserved: 0
            0x03, 0x00, // bitmap: 0x0003 (slots 0,1)
            0x02, 0x00, 0x00, 0x00, // length: 2
            0x06, 0x14, // value 0: arr (packed, 1 byte), offset=0x14 (20)
            0x06, 0x30, // value 1: arr (packed, 1 byte), offset=0x30 (48)
            // Child 0 at offset 0x14 (20): arr leaf containing i64(42)
            0x1D, 0x00, 0x00, 0x00, // header: node_len=28, leaf=1, arr=0
            0x01, 0x00, 0x00, 0x00, // entry_count: 1
            0x00, // shift: 0
            0x00, // reserved: 0
            0x01, 0x00, // bitmap: 0x0001 (slot 0)
            0x01, 0x00, 0x00, 0x00, // length: 1
            0x02, 0x2A, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // i64(42)
            0x00, 0x00, 0x00, // padding to 4-byte boundary
            // Child 1 at offset 0x30 (48): arr leaf containing i64(99)
            0x1D, 0x00, 0x00, 0x00, // header: node_len=28, leaf=1, arr=0
            0x01, 0x00, 0x00, 0x00, // entry_count: 1
            0x00, // shift: 0
            0x00, // reserved: 0
            0x01, 0x00, // bitmap: 0x0001 (slot 0)
            0x01, 0x00, 0x00, 0x00, // length: 1
            0x02, 0x63, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // i64(99)
            0x00, 0x00, 0x00, // padding to 4-byte boundary
        ];

        // Parse root node
        let root = ArrLeafNodeRef::new(&data).unwrap();
        assert_eq!(root.value_count(), 2);

        // Get nested arr offsets
        let arr0 = root.value_at(0).unwrap();
        let arr1 = root.value_at(1).unwrap();
        assert_eq!(arr0, ValueType::Arr(0x14));
        assert_eq!(arr1, ValueType::Arr(0x30));

        // Parse child nodes at those offsets
        let ValueType::Arr(offset0) = arr0 else {
            panic!()
        };
        let child0 = ArrLeafNodeRef::new(&data[offset0 as usize..]).unwrap();
        assert_eq!(child0.value_count(), 1);
        assert_eq!(child0.value_at(0), Some(ValueType::I64(42)));

        let ValueType::Arr(offset1) = arr1 else {
            panic!()
        };
        let child1 = ArrLeafNodeRef::new(&data[offset1 as usize..]).unwrap();
        assert_eq!(child1.value_count(), 1);
        assert_eq!(child1.value_at(0), Some(ValueType::I64(99)));
    }

    // ArrBranchNodeRef
    #[test]
    fn arr_branch_with_children() {
        let data = [
            0x1C, 0x00, 0x00, 0x00, // header: node_len=28 (0x1C), branch=0, arr=0
            0x02, 0x00, 0x00, 0x00, // entry_count: 2
            0x04, // shift: 4
            0x00, // reserved: 0
            0x03, 0x00, // bitmap: 0x0003 (slots 0,1)
            0x10, 0x00, 0x00, 0x00, // length: 16
            0x20, 0x00, 0x00, 0x00, // child 0 offset: 0x20
            0x40, 0x00, 0x00, 0x00, // child 1 offset: 0x40
        ];
        let node = ArrBranchNodeRef::new(&data).unwrap();
        assert_eq!(node.shift(), 4);
        assert_eq!(node.bitmap(), Some(0x0003));
        assert_eq!(node.length(), Some(16));
        assert_eq!(node.child_count(), 2);
        assert_eq!(node.child_offset(0), Some(0x20));
        assert_eq!(node.child_offset(1), Some(0x40));
        assert_eq!(node.child_offset(2), None);
    }

    // MapBranchNodeRef
    #[test]
    fn map_branch_with_children() {
        let data = [
            0x16, 0x00, 0x00, 0x00, // header: node_len=20, branch=0, map=1
            0x02, 0x00, 0x00, 0x00, // entry_count: 2
            0x21, 0x00, // bitmap: 0x0021 (slots 0, 5)
            0x00, 0x00, // reserved
            0x20, 0x00, 0x00, 0x00, // child 0 offset: 0x20
            0x40, 0x00, 0x00, 0x00, // child 1 offset: 0x40
        ];
        let node = MapBranchNodeRef::new(&data).unwrap();
        assert_eq!(node.bitmap(), Some(0x0021));
        assert_eq!(node.child_count(), 2);
        assert_eq!(node.child_offset(0), Some(0x20));
        assert_eq!(node.child_offset(1), Some(0x40));
        assert_eq!(node.child_offset(2), None);
    }

    // MapLeafNodeRef
    #[test]
    fn map_leaf_with_entries() {
        let data = [
            0x1F, 0x00, 0x00, 0x00, // header: node_len=28, leaf=1, map=1
            0x02, 0x00, 0x00, 0x00, // entry_count: 2
            // entry 0: key="a", value=i64(42)
            0x1C, 0x61, // txt "a" (packed, len=1)
            0x02, 0x2A, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // i64(42)
            // entry 1: key="b", value=i64(99)
            0x1C, 0x62, // txt "b" (packed, len=1)
            0x02, 0x63, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // i64(99)
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // padding
        ];
        let node = MapLeafNodeRef::new(&data).unwrap();
        assert_eq!(node.entry_count(), 2);
        assert_eq!(node.key_at(0), Some("a"));
        assert_eq!(node.key_at(1), Some("b"));
        assert_eq!(node.value_at(0), Some(ValueType::I64(42)));
        assert_eq!(node.value_at(1), Some(ValueType::I64(99)));
        assert_eq!(node.get("a"), Some(ValueType::I64(42)));
        assert_eq!(node.get("b"), Some(ValueType::I64(99)));
        assert_eq!(node.get("c"), None);
    }

    #[test]
    fn map_leaf_with_nested_map() {
        let data = [
            // Root map leaf at offset 0x00: {"inner": map@0x14}
            0x17, 0x00, 0x00, 0x00, // header: node_len=20, leaf=1, map=1
            0x01, 0x00, 0x00, 0x00, // entry_count: 1
            // entry: key="inner", value=map@0x14
            0x5C, 0x69, 0x6E, 0x6E, 0x65, 0x72, // txt "inner" (packed, len=5)
            0x07, 0x14, // map (packed, 1 byte), offset=0x14 (20)
            0x00, 0x00, 0x00, 0x00, // padding to reach offset 0x14
            // Child map leaf at offset 0x14 (20): {"x": 123}
            0x17, 0x00, 0x00, 0x00, // header: node_len=20, leaf=1, map=1
            0x01, 0x00, 0x00, 0x00, // entry_count: 1
            0x1C, 0x78, // txt "x" (packed, len=1)
            0x02, 0x7B, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // i64(123)
            0x00, 0x00, 0x00, // padding
        ];

        // Parse root
        let root = MapLeafNodeRef::new(&data).unwrap();
        assert_eq!(root.entry_count(), 1);
        assert_eq!(root.key_at(0), Some("inner"));

        // Get nested map offset
        let inner = root.get("inner").unwrap();
        assert_eq!(inner, ValueType::Map(0x14));

        // Parse child map
        let ValueType::Map(offset) = inner else {
            panic!()
        };
        let child = MapLeafNodeRef::new(&data[offset as usize..]).unwrap();
        assert_eq!(child.entry_count(), 1);
        assert_eq!(child.key_at(0), Some("x"));
        assert_eq!(child.get("x"), Some(ValueType::I64(123)));
    }

    #[test]
    fn map_slot_hash() {
        // xxh32("foo", 0) = 0xE3069283 (verify with reference impl)
        // slot at depth 0: (hash >> 0) & 0xF
        // slot at depth 1: (hash >> 4) & 0xF
        use crate::xxh32::xxh32;
        let hash = xxh32(b"foo", 0);
        assert_eq!(map_slot("foo", 0), (hash & 0xF) as u8);
        assert_eq!(map_slot("foo", 1), ((hash >> 4) & 0xF) as u8);
    }
}

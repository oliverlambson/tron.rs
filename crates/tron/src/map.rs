use crate::value::ValueNode;

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
    todo!()
}

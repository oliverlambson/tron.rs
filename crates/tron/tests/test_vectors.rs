//! Tests using the `value_nodes.json` test vectors.

use serde::Deserialize;
use tron::value::{TypedValue, Value};

fn hex_to_bytes(hex: &str) -> Vec<u8> {
    (0..hex.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&hex[i..i + 2], 16).unwrap())
        .collect()
}

#[derive(Deserialize)]
struct TestVectors {
    nil: Vec<NilTest>,
    bit: Vec<BitTest>,
    i64: Vec<I64Test>,
    f64: Vec<F64Test>,
    txt: Vec<TxtTest>,
    bin: Vec<BinTest>,
    arr: Vec<ArrTest>,
    map: Vec<MapTest>,
    header: Vec<HeaderTest>,
    footer: Vec<FooterTest>,
}

#[derive(Deserialize)]
struct NilTest {
    bytes: String,
    #[allow(dead_code)]
    parsed: NilParsed,
}

#[derive(Deserialize)]
struct NilParsed {}

#[derive(Deserialize)]
struct BitTest {
    bytes: String,
    parsed: BitParsed,
}

#[derive(Deserialize)]
struct BitParsed {
    value: bool,
}

#[derive(Deserialize)]
struct I64Test {
    bytes: String,
    parsed: I64Parsed,
}

#[derive(Deserialize)]
struct I64Parsed {
    value: i64,
}

#[derive(Deserialize)]
struct F64Test {
    bytes: String,
    parsed: F64Parsed,
}

#[derive(Deserialize)]
struct F64Parsed {
    value: f64,
}

#[derive(Deserialize)]
struct TxtTest {
    bytes: String,
    parsed: TxtParsed,
}

#[derive(Deserialize)]
struct TxtParsed {
    value: String,
}

#[derive(Deserialize)]
struct BinTest {
    bytes: String,
    parsed: BinParsed,
}

#[derive(Deserialize)]
struct BinParsed {
    value: String, // hex-encoded
}

#[derive(Deserialize)]
struct ArrTest {
    bytes: String,
    parsed: ArrParsed,
}

#[derive(Deserialize)]
struct ArrParsed {
    is_root: bool,
    is_branch: bool,
    node_len: u32,
    shift: u8,
    bitmap: u16,
    length: Option<u32>,
    entries: Vec<u32>,
}

#[derive(Deserialize)]
struct MapTest {
    bytes: String,
    parsed: MapParsed,
}

#[derive(Deserialize)]
struct MapParsed {
    is_branch: bool,
    node_len: u32,
    bitmap: Option<u32>,
    entries: Vec<MapEntry>,
}

#[derive(Deserialize)]
#[serde(untagged)]
enum MapEntry {
    Leaf { key: u32, value: u32 },
    Branch(u32),
}

#[derive(Deserialize)]
struct HeaderTest {
    bytes: String,
    parsed: HeaderParsed,
}

#[derive(Deserialize)]
struct HeaderParsed {
    magic: String,
}

#[derive(Deserialize)]
struct FooterTest {
    bytes: String,
    parsed: FooterParsed,
}

#[derive(Deserialize)]
struct FooterParsed {
    root_address: u32,
    prev_root_address: u32,
}

fn load_test_vectors() -> TestVectors {
    let json = include_str!("../../../tron-shared/shared/testdata/tron/value_nodes.json");
    serde_json::from_str(json).expect("Failed to parse test vectors")
}

#[test]
fn test_nil_vectors() {
    let vectors = load_test_vectors();

    for test in &vectors.nil {
        let bytes = hex_to_bytes(&test.bytes);
        let value = Value::new(&bytes, 0).expect("Failed to create Value");
        assert!(
            matches!(value.typed(), Ok(TypedValue::Nil)),
            "Expected nil for bytes: {}",
            test.bytes
        );
    }
}

#[test]
fn test_bit_vectors() {
    let vectors = load_test_vectors();

    for test in &vectors.bit {
        let bytes = hex_to_bytes(&test.bytes);
        let value = Value::new(&bytes, 0).expect("Failed to create Value");
        match value.typed().unwrap() {
            TypedValue::Bool(b) => {
                assert_eq!(b, test.parsed.value, "Wrong value for: {}", test.bytes)
            }
            _ => panic!("Expected Bool for: {}", test.bytes),
        }
    }
}

#[test]
fn test_i64_vectors() {
    let vectors = load_test_vectors();

    for test in &vectors.i64 {
        let bytes = hex_to_bytes(&test.bytes);
        let value = Value::new(&bytes, 0).expect("Failed to create Value");
        match value.typed().unwrap() {
            TypedValue::I64(n) => assert_eq!(
                n, test.parsed.value,
                "Wrong value for bytes: {}, expected: {}",
                test.bytes, test.parsed.value
            ),
            _ => panic!("Expected I64 for: {}", test.bytes),
        }
    }
}

#[test]
fn test_f64_vectors() {
    let vectors = load_test_vectors();

    for test in &vectors.f64 {
        let bytes = hex_to_bytes(&test.bytes);
        let value = Value::new(&bytes, 0).expect("Failed to create Value");
        match value.typed().unwrap() {
            TypedValue::F64(actual) => assert!(
                (actual - test.parsed.value).abs() < 1e-15,
                "Wrong value for bytes: {}, expected: {}, got: {}",
                test.bytes,
                test.parsed.value,
                actual
            ),
            _ => panic!("Expected F64 for: {}", test.bytes),
        }
    }
}

#[test]
fn test_txt_vectors() {
    let vectors = load_test_vectors();

    for test in &vectors.txt {
        let bytes = hex_to_bytes(&test.bytes);
        let value = Value::new(&bytes, 0).expect("Failed to create Value");
        match value.typed().unwrap() {
            TypedValue::Str(s) => assert_eq!(
                s, test.parsed.value,
                "Wrong value for bytes: {}, expected: {:?}",
                test.bytes, test.parsed.value
            ),
            _ => panic!("Expected Str for: {}", test.bytes),
        }
    }
}

#[test]
fn test_bin_vectors() {
    let vectors = load_test_vectors();

    for test in &vectors.bin {
        let bytes = hex_to_bytes(&test.bytes);
        let value = Value::new(&bytes, 0).expect("Failed to create Value");
        let expected_bytes = hex_to_bytes(&test.parsed.value);
        match value.typed().unwrap() {
            TypedValue::Bytes(b) => assert_eq!(
                b,
                expected_bytes.as_slice(),
                "Wrong value for bytes: {}",
                test.bytes
            ),
            _ => panic!("Expected Bytes for: {}", test.bytes),
        }
    }
}

#[test]
fn test_arr_vectors() {
    let vectors = load_test_vectors();

    for test in &vectors.arr {
        let bytes = hex_to_bytes(&test.bytes);
        let value = Value::new(&bytes, 0).expect("Failed to create Value");
        let Ok(TypedValue::Arr(arr)) = value.typed() else {
            panic!("Expected Arr for: {}", test.bytes)
        };
        assert_eq!(
            arr.is_root(),
            test.parsed.is_root,
            "Wrong is_root for: {}",
            test.bytes
        );
        assert_eq!(
            arr.is_branch(),
            test.parsed.is_branch,
            "Wrong is_branch for: {}",
            test.bytes
        );
        assert_eq!(
            arr.node_len(),
            test.parsed.node_len,
            "Wrong node_len for: {}",
            test.bytes
        );
        assert_eq!(
            arr.shift(),
            test.parsed.shift,
            "Wrong shift for: {}",
            test.bytes
        );
        assert_eq!(
            arr.bitmap(),
            test.parsed.bitmap,
            "Wrong bitmap for: {}",
            test.bytes
        );

        if test.parsed.is_root {
            assert_eq!(
                arr.length(),
                test.parsed.length,
                "Wrong length for: {}",
                test.bytes
            );
        }

        // Check entries
        for (i, expected_addr) in test.parsed.entries.iter().enumerate() {
            let actual = arr.get_entry_addr(i);
            assert_eq!(
                actual,
                Some(*expected_addr),
                "Wrong entry {} for: {}",
                i,
                test.bytes
            );
        }
    }
}

#[test]
fn test_map_vectors() {
    use tron::value::MapNode;

    let vectors = load_test_vectors();

    for test in &vectors.map {
        let bytes = hex_to_bytes(&test.bytes);
        let value = Value::new(&bytes, 0).expect("Failed to create Value");
        let Ok(TypedValue::Map(map)) = value.typed() else {
            panic!("Expected Map for: {}", test.bytes)
        };

        assert_eq!(
            map.node_len(),
            test.parsed.node_len,
            "Wrong node_len for: {}",
            test.bytes
        );

        match map {
            MapNode::Branch(branch) => {
                assert!(
                    test.parsed.is_branch,
                    "Expected branch but got leaf for: {}",
                    test.bytes
                );
                assert_eq!(
                    Some(branch.bitmap()),
                    test.parsed.bitmap,
                    "Wrong bitmap for: {}",
                    test.bytes
                );

                // Check branch child entries
                for (i, entry) in test.parsed.entries.iter().enumerate() {
                    if let MapEntry::Branch(addr) = entry {
                        let actual = branch.get_child_addr(i);
                        assert_eq!(actual, Some(*addr), "Wrong child {} for: {}", i, test.bytes);
                    }
                }
            }
            MapNode::Leaf(leaf) => {
                assert!(
                    !test.parsed.is_branch,
                    "Expected leaf but got branch for: {}",
                    test.bytes
                );

                let kv_pairs: Vec<_> = leaf.kv_pairs().collect();
                assert_eq!(
                    kv_pairs.len(),
                    test.parsed.entries.len(),
                    "Wrong entry count for: {}",
                    test.bytes
                );

                for (i, entry) in test.parsed.entries.iter().enumerate() {
                    if let MapEntry::Leaf { key, value } = entry {
                        assert_eq!(
                            kv_pairs[i],
                            (*key, *value),
                            "Wrong kv pair {} for: {}",
                            i,
                            test.bytes
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn test_header_vectors() {
    let vectors = load_test_vectors();

    for test in &vectors.header {
        let bytes = hex_to_bytes(&test.bytes);
        assert_eq!(bytes.len(), 4, "Header should be 4 bytes");

        // Parse header magic
        let magic = std::str::from_utf8(&bytes).expect("Invalid magic");
        assert_eq!(magic, test.parsed.magic, "Wrong magic for: {}", test.bytes);
    }
}

#[test]
fn test_footer_vectors() {
    let vectors = load_test_vectors();

    for test in &vectors.footer {
        let bytes = hex_to_bytes(&test.bytes);
        assert_eq!(bytes.len(), 8, "Footer should be 8 bytes");

        // Parse footer fields
        let root_addr = u32::from_le_bytes(bytes[0..4].try_into().unwrap());
        let prev_root_addr = u32::from_le_bytes(bytes[4..8].try_into().unwrap());

        assert_eq!(
            root_addr, test.parsed.root_address,
            "Wrong root_address for: {}",
            test.bytes
        );
        assert_eq!(
            prev_root_addr, test.parsed.prev_root_address,
            "Wrong prev_root_address for: {}",
            test.bytes
        );
    }
}

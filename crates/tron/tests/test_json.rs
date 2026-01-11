//! Tests using the `documents.json` test vectors.

use serde::Deserialize;
use tron::{from_json, to_json};

fn hex_to_bytes(hex: &str) -> Vec<u8> {
    (0..hex.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&hex[i..i + 2], 16).unwrap())
        .collect()
}

#[derive(Deserialize)]
struct DocumentTest {
    description: String,
    json: serde_json::Value,
    tron: String,
}

#[test]
fn test_document_vectors_roundtrip() {
    let json = include_str!("../../../tron-shared/shared/testdata/tron/documents.json");
    let cases: Vec<DocumentTest> =
        serde_json::from_str(json).expect("Failed to parse test vectors");

    for case in &cases {
        let json_str = serde_json::to_string(&case.json).unwrap();

        let doc = from_json(&json_str)
            .unwrap_or_else(|e| panic!("from_json failed for '{}': {}", case.description, e));

        let result_str = to_json(&doc)
            .unwrap_or_else(|e| panic!("to_json failed for '{}': {}", case.description, e));

        assert_eq!(
            json_str, result_str,
            "Roundtrip failed for '{}'",
            case.description
        );
    }
}

#[test]
fn test_document_vectors_bytes() {
    let json = include_str!("../../../tron-shared/shared/testdata/tron/documents.json");
    let cases: Vec<DocumentTest> =
        serde_json::from_str(json).expect("Failed to parse test vectors");

    for case in &cases {
        let expected_bytes = hex_to_bytes(&case.tron);

        let json_str = serde_json::to_string(&case.json).unwrap();

        let doc = from_json(&json_str)
            .unwrap_or_else(|e| panic!("from_json failed for '{}': {}", case.description, e));

        assert_eq!(
            doc.as_bytes(),
            &expected_bytes[..],
            "Byte mismatch for '{}'\nExpected: {:02x?}\nActual:   {:02x?}",
            case.description,
            expected_bytes,
            doc.as_bytes()
        );
    }
}

//! Example of using the low-level API for nested object access.
//!
//! cargo run --package tron --example nested_access

use tron::{TypedValue, Value, arr, from_json, map};

fn main() -> Result<(), tron::Error> {
    let doc = from_json(r#"{"users": [{"name": "Amy"}, {"name": "Bob"}]}"#)?;

    // node = root
    let mut addr = doc.root_addr();
    let TypedValue::Map(node) = Value::new(doc.as_bytes(), addr)?.typed()? else {
        panic!()
    };

    // node = root["users"]
    addr = map::map_get(doc.as_bytes(), node.addr(), "users")?.unwrap();
    let TypedValue::Arr(node) = Value::new(doc.as_bytes(), addr)?.typed()? else {
        panic!()
    };

    // node = root["users"][1]
    addr = arr::arr_get(doc.as_bytes(), node.addr(), 1)?.unwrap();
    let TypedValue::Map(node) = Value::new(doc.as_bytes(), addr)?.typed()? else {
        panic!()
    };

    // node = root["users"][1]["name"]
    addr = map::map_get(doc.as_bytes(), node.addr(), "name")?.unwrap();
    let TypedValue::Str(name) = Value::new(doc.as_bytes(), addr)?.typed()? else {
        panic!()
    };

    println!("{name}");
    Ok(())
}

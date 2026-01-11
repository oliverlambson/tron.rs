pub mod arr;
pub mod document;
pub mod encode;
pub mod footer;
pub mod map;
pub mod value;
pub(crate) mod xxh32;

pub fn hello_from_bin() -> String {
    "Hello from bin".to_string()
}

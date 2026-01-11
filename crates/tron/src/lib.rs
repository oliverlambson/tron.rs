pub mod document;
pub mod node;
pub mod scalar;
pub mod trailer;
pub mod tree;
pub mod value;
pub(crate) mod xxh32;

pub fn hello_from_bin() -> String {
    "Hello from bin".to_string()
}

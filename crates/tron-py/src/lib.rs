use pyo3::prelude::*;

#[pymodule]
mod _core {
    use pyo3::prelude::*;

    #[pyfunction]
    fn hello_from_bin() -> String {
        tron::hello_from_bin()
    }
}

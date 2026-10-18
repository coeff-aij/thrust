//@compile-flags: -C debug-assertions=off

// `#[thrust::callable]` is a contract written without the macros; with `#[thrust::ignored]` it is
// rejected as `requires`/`ensures` are.

#[thrust::ignored]
#[thrust::callable]
fn h(x: i32) -> i32 { //~ ERROR: `#[thrust::ignored]` cannot have a contract
    x
}

fn main() {
    let _ = h(1);
}

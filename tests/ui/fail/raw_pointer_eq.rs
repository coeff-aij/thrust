//@compile-flags: -C debug-assertions=off

// A raw pointer is opaque: comparing two is not supported.
#[thrust::callable]
fn same(p: *const i32, q: *const i32) -> bool {
    p == q //~ ERROR: comparing or computing with a raw or function pointer is not supported
}

fn main() {}

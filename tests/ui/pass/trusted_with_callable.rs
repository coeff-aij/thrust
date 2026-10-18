//@check-pass
//@compile-flags: -C debug-assertions=off

// The twin of `fail/ignored_with_callable.rs`: `#[thrust::trusted]` with `#[thrust::callable]`
// trusts that `h` accepts any argument and does not panic.

#[thrust::trusted]
#[thrust::callable]
fn h(x: i32) -> i32 {
    x
}

fn main() {
    let _ = h(1);
}

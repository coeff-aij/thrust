//@check-pass
//@compile-flags: -C debug-assertions=off
// The twin of `fail/uncontracted_under_trusted.rs`: a written contract is the trusted caller's
// to meet.

#[thrust_macros::requires(x > 0)]
#[thrust_macros::ensures(true)]
fn g(x: i32) {
    assert!(x > 0);
}

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn t() {
    g(1)
}

fn main() {
    t()
}

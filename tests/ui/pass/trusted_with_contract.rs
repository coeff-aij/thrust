//@check-pass
//@compile-flags: -C debug-assertions=off

// The twin of `fail/ignored_with_contract.rs`: `#[thrust::trusted]` keeps the contract and does not
// check the body.

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == 1)]
fn f() -> i32 {
    1
}

fn main() {
    assert!(f() == 1);
}

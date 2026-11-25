//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// The twin of `fail/block_contract_inline_unlisted_copy_of_listed.rs`: the copy of the listed
// variable is not named like a function of the module, and the body calls the module's `foo`.
fn foo(a: i64) -> i64 {
    a + 10
}

#[thrust_macros::context]
fn host<F: Fn(i64) -> i64 + Copy>(f: F) -> i64 {
    let copy = f;
    let _ = &copy;
    thrust_macros::block_contract_inline!(
        |f: F| -> i64 requires(true), ensures(result == 11), { foo(1) }
    )
}

fn main() {}

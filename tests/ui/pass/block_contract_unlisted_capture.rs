//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// The twin of `fail/block_contract_unlisted_capture.rs`: the block lists the captured
// variable it uses.
fn foo(a: i64) -> i64 {
    a + 10
}

#[thrust_macros::context]
fn host(n: i64) -> i64 {
    let c = move |k: i64| {
        thrust_macros::block_contract!(
            |k: i64, n: i64| -> i64 requires(true), ensures(result == k + n + 10), { foo(k) + n }
        )
    };
    c(1)
}

fn main() {}

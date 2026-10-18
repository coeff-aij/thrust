//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A trusted closure written in the non-generic `main` is trusted throughout, as a non-generic
// trusted function is, and may run an ignored function.

#![feature(stmt_expr_attributes)]

#[thrust::ignored]
fn bad() -> i32 {
    1
}

fn main() {
    let c = #[thrust::trusted]
    #[thrust::callable]
    || {
        bad();
    };
    c();
}

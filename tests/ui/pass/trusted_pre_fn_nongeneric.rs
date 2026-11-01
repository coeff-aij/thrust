//@check-pass
//@compile-flags: -C debug-assertions=off
// The twin of `fail/trusted_pre_fn_nongeneric.rs`: a non-generic trusted function states `pre!`
// of a function, and its caller discharges it, so the function need not accept other arguments.

fn g(x: i32) {
    assert!(x > 0)
}

#[thrust::trusted]
#[thrust_macros::requires(thrust_macros::pre!(g(x)))]
#[thrust_macros::ensures(true)]
fn t1(x: i32) {
    g(x)
}

fn main() {
    t1(1)
}

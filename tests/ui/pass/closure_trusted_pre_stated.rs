//@check-pass
//@compile-flags: -C debug-assertions=off
// The twin of `fail/closure_trusted_pre_stated.rs`: the stated `pre!` holds at the call, and the
// closure need not accept other arguments.

#[thrust::trusted]
#[thrust_macros::requires(thrust_macros::pre!(f(x)))]
#[thrust_macros::ensures(true)]
fn apply_pre<F: Fn(i32)>(f: F, x: i32) {
    f(x)
}

fn main() {
    apply_pre(|x: i32| assert!(x > 0), 1);
}

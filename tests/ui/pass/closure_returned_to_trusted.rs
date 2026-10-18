//@check-pass
//@compile-flags: -C debug-assertions=off
// The twin of `fail/closure_returned_to_trusted.rs`: the closure's precondition is written, so
// the trusted body that runs it is trusted to meet it.

#[thrust::trusted]
#[thrust_macros::requires(thrust_macros::pre!(f(x)))]
#[thrust_macros::ensures(true)]
fn apply_pre<F: Fn(i32)>(f: F, x: i32) {
    f(x)
}

fn mk() -> impl Fn(i32) {
    thrust_macros::closure!(requires(x > 0), |x: i32| assert!(x > 0))
}

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn t() {
    let f = mk();
    f(1)
}

fn main() {
    apply_pre(mk(), 1);
    t()
}

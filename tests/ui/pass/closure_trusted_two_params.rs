//@check-pass
//@compile-flags: -C debug-assertions=off
// The twin of `fail/closure_trusted_two_params.rs`.

#[thrust::trusted]
#[thrust_macros::requires(thrust_macros::pre!(f(x)))]
#[thrust_macros::ensures(true)]
fn apply2<F: Fn(i32), G: Fn(i32)>(f: F, g: G, x: i32) {
    f(x);
    g(x)
}

fn main() {
    apply2(|x: i32| assert!(x > 0), |_: i32| (), 1);
}

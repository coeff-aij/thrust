//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// `f` and `g` are both of type `F`. The `pre!` stated of `f` does not count for `g`, a value with
// other captures, nor, since the type is held twice, for `f`: both must accept every argument,
// which they do here.

#[thrust::trusted]
#[thrust_macros::requires(thrust_macros::pre!(f(x)))]
#[thrust_macros::ensures(true)]
fn apply<F: Fn(i32)>(f: F, g: F, x: i32) {
    f(x);
    g(x)
}

fn main() {
    let mk = |k: i32| move |x: i32| assert!(k == 0 || x > 0);
    apply(mk(0), mk(0), 0);
}

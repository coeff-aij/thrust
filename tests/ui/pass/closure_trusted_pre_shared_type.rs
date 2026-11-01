//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// `F` and `G` are instantiated with the same closure type. The `pre!` stated of `f` does not count
// for `g`, a value with other captures, nor, since the type is shared, for `f`: both must accept
// every argument, which they do here.

#[thrust::trusted]
#[thrust_macros::requires(thrust_macros::pre!(f(x)))]
#[thrust_macros::ensures(true)]
fn apply2<F: Fn(i32), G: Fn(i32)>(f: F, g: G, x: i32) {
    f(x);
    g(x)
}

fn main() {
    let mk = |k: i32| move |x: i32| assert!(k == 0 || x > 0);
    apply2(mk(0), mk(0), 0);
}

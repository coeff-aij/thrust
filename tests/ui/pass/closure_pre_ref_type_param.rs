//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// `G` is instantiated with `&H` for a closure type parameter `H` of the caller: `pre!` of `g` is
// `H`'s, whose `Fn` bound is among the caller's predicates.

#[thrust::trusted]
#[thrust_macros::requires(thrust_macros::pre!(g(x)))]
#[thrust_macros::ensures(thrust_macros::post!(g(x), result))]
fn apply<G: Fn(i32) -> i32>(g: G, x: i32) -> i32 {
    g(x)
}

#[thrust::callable]
#[thrust_macros::requires(thrust_macros::pre!(f(0)))]
fn h<H: Fn(i32) -> i32>(f: &H) -> i32 {
    apply(f, 0)
}

fn main() {
    let a = move |x: i32| x + 1;
    let _ = h(&a);
}

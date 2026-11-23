//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// A block contract names a closure local as `|f: _|`, as `assume!` does. The code under the
// contract starts from `requires` alone, whose `pre!` of `f` at 5 is what `apply` requires;
// its `ensures` gives the `post!` after it.

#[thrust::trusted]
#[thrust_macros::requires(thrust_macros::pre!(g(x)))]
#[thrust_macros::ensures(thrust_macros::post!(g(x), result))]
fn apply<G: Fn(i64) -> i64>(g: G, x: i64) -> i64 {
    g(x)
}

#[thrust_macros::requires(n < 5)]
fn run(n: i64) -> i64 {
    let f = thrust_macros::closure!(
        captures(n: i64),
        requires(x > n),
        ensures(result == x + n),
        |x: i64| -> i64 { x + n },
    );
    let mut r = 0;
    thrust_macros::block_contract!(
        requires(|f: _| thrust_macros::pre!(f(5i64))),
        ensures(|f: _, r: i64| thrust_macros::post!(f(5i64), r)),
        {
            r = apply(f, 5);
        }
    );
    assert!(r == 5 + n);
    r
}

fn main() {
    let _ = run(0);
}

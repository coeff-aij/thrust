//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// A block contract names a closure local as `|f: _|`, as `assume!` does. With `n` up to 5, the
// `pre!` of `f` at 5 that `block_requires!` states does not hold where it is written.

#[thrust::trusted]
#[thrust_macros::requires(thrust_macros::pre!(g(x)))]
#[thrust_macros::ensures(thrust_macros::post!(g(x), result))]
fn apply<G: Fn(i64) -> i64>(g: G, x: i64) -> i64 {
    g(x)
}

#[thrust_macros::requires(n <= 5)]
fn run(n: i64) -> i64 {
    let f = thrust_macros::closure!(
        captures(n: i64),
        requires(x > n),
        ensures(result == x + n),
        |x: i64| -> i64 { x + n },
    );
    let mut r = 0;
    thrust_macros::block_requires!(|f: _| thrust_macros::pre!(f(5i64)));
    r = apply(f, 5);
    thrust_macros::block_ensures!(|f: _, r: i64| thrust_macros::post!(f(5i64), r));
    assert!(r == 5 + n);
    r
}

fn main() {
    let _ = run(0);
}

//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// In a generic function, `assume!(|f: _| ..)` names a closure local, whose type cannot be written. The assumed `pre!`
// of `f` at 5 says `n < 5`, which `apply`'s precondition at 5 then follows.

#[thrust::trusted]
#[thrust_macros::requires(thrust_macros::pre!(g(x)))]
#[thrust_macros::ensures(thrust_macros::post!(g(x), result))]
fn apply<G: Fn(i64) -> i64>(g: G, x: i64) -> i64 {
    g(x)
}

#[thrust_macros::requires(true)]
fn run<T>(n: i64) -> i64 {
    let f = thrust_macros::closure!(
        captures(n: i64),
        requires(x > n),
        ensures(result == x + n),
        |x: i64| -> i64 { x + n },
    );
    thrust_macros::assume!(|f: _| thrust_macros::pre!(f(5i64)));
    apply(f, 5)
}

fn main() {
    let _ = run::<u8>(0);
}

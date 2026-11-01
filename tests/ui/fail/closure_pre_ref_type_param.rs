//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// The twin of `pass/closure_pre_ref_type_param.rs`: the caller requires the closure's precondition
// at `1` but calls `apply` with `0`, so it fails only if `apply`'s precondition at `G = &H` is the
// closure's precondition at `0`.

#[thrust::trusted]
#[thrust_macros::requires(thrust_macros::pre!(g(x)))]
#[thrust_macros::ensures(thrust_macros::post!(g(x), result))]
fn apply<G: Fn(i32) -> i32>(g: G, x: i32) -> i32 {
    g(x)
}

#[thrust::callable]
#[thrust_macros::requires(thrust_macros::pre!(f(1)))]
fn h<H: Fn(i32) -> i32>(f: &H) -> i32 {
    apply(f, 0)
}

fn main() {
    let a = move |x: i32| x + 1;
    let _ = h(&a);
}

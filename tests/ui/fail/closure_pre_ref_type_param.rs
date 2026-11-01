//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// The twin of `pass/closure_pre_ref_type_param.rs`: the closure behind the reference rejects the
// argument that the caller's `requires` allows.

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
    let a = move |x: i32| { assert!(x > 5); x + 1 };
    let _ = h(&a);
}

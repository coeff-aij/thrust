//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
// The twin of `pass/closure_trusted_pre_ref_arg.rs`: the closure behind the reference rejects the
// argument `apply` calls it with.

#[thrust::trusted]
#[thrust_macros::requires(thrust_macros::pre!(g(x)))]
#[thrust_macros::ensures(thrust_macros::post!(g(x), result))]
fn apply<G: Fn(i32) -> i32>(g: G, x: i32) -> i32 {
    g(x)
}

fn main() {
    let k = 3;
    let a = move |x: i32| {
        assert!(x > k);
        x + k
    };
    assert!(apply(&a, 3) == 6);
}

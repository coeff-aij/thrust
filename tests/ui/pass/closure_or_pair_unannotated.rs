//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
use thrust_models::forall;

// The closures in `main` have no contract, so at the call `pre!` and `post!` of `p` and `q` are
// unknowns, and `either`'s body is analyzed again with them. Only that analysis puts the unknowns
// under the `requires`' universal in a body and the first `ensures`' disjunction in a head, and
// each path there holds the disjunct it proves; the generic check is Horn.
#[thrust_macros::requires(forall(|j: i64| thrust_macros::pre!(p(j)) && thrust_macros::pre!(q(j))))]
#[thrust_macros::ensures(result ==> thrust_macros::post!(p(x), true) || thrust_macros::post!(q(x), true))]
#[thrust_macros::ensures(!result ==> thrust_macros::post!(p(x), false) && thrust_macros::post!(q(x), false))]
fn either<P: Fn(i64) -> bool, Q: Fn(i64) -> bool>(p: &P, q: &Q, x: i64) -> bool {
    p(x) || q(x)
}

fn main() {
    let p = |x: i64| x >= 4;
    let q = |x: i64| x == 2;
    let b = either(&p, &q, 2);
    assert!(b);
}

//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60 THRUST_CANDIDATE_ATOMS=2

// With THRUST_CANDIDATE_ATOMS=2 the entry clauses of the loop head have unknowns in their body
// (`pre!(g(x))`); an atom that applied one made the solver stop without a verdict.
#[thrust_macros::requires(thrust_macros::pre!(g(x)) && thrust_macros::pre!(h(x)))]
#[thrust_macros::ensures(thrust_macros::post!(g(x), result) || thrust_macros::post!(h(x), result))]
fn alternate<G: Fn(i64) -> i64, H: Fn(i64) -> i64>(g: &G, h: &H, x: i64, n: i64) -> i64 {
    let mut r = g(x);
    let mut use_h = true;
    let mut i = 0_i64;
    while i < n {
        if use_h {
            r = h(x);
        } else {
            r = g(x);
        }
        use_h = !use_h;
        i += 1;
    }
    r
}

fn main() {
    let g = |x: i64| x + 1;
    let h = |x: i64| x - 1;
    let r = alternate(&g, &h, 5, 3);
    assert!(r == 6 || r == 4);
}

//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A binder in the variant that has a parameter's name is the binder: the variant here is `m`, not
// `n`, so it does not decrease at `f(n, n - 1)` from an unconstrained `m`.
#[thrust_macros::lemma]
#[thrust_macros::variant(match m { n => n })]
#[thrust_macros::requires(n >= 0)]
#[thrust_macros::ensures(false)]
fn f(n: i64, m: i64) {
    f(n, n - 1);
}

fn main() {}

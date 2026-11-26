//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A recursive call at an argument that does not decrease the variant is an Unsat obligation.
#[thrust_macros::lemma]
#[thrust_macros::variant(n)]
#[thrust_macros::requires(n >= 0)]
#[thrust_macros::ensures(false)]
fn bad(n: i64) {
    bad(n)
}

fn main() {}

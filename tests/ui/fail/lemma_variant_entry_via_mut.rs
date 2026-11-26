//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The variant at the recursive call's argument is compared with the variant at the parameter's
// value on entry, not with a value the body re-pointed a reference to: `n + 1` does not decrease.
#[thrust_macros::lemma]
#[thrust_macros::variant(n)]
#[thrust_macros::requires(n >= 0)]
#[thrust_macros::ensures(false)]
fn bad(n: i64) {
    let big = n + 1;
    let mut r = &n;
    {
        let m = &mut r;
        *m = &big;
    }
    bad(*r);
}

fn main() {}

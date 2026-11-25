//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A variant may bind names that are not a parameter's; the binder's reads stay its own.
#[thrust_macros::lemma]
#[thrust_macros::variant(match m { k => k })]
#[thrust_macros::requires(n >= 0 && m >= 0)]
#[thrust_macros::ensures(n >= 0)]
fn f(n: i64, m: i64) {
    if m > 0 {
        f(n, m - 1);
    }
}

fn main() {
    thrust_macros::proof!(f(1, 2));
}

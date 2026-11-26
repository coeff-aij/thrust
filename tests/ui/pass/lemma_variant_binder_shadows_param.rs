//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A binder in the variant that has a parameter's name is the binder: the variant is `m`, which
// decreases at `f(n, m - 1)`.
#[thrust_macros::lemma]
#[thrust_macros::variant(match m { n => n })]
#[thrust_macros::requires(n >= 0 && m >= 0)]
#[thrust_macros::ensures(n >= 0)]
fn f(n: i64, m: i64) {
    if m > 0 {
        f(n, m - 1);
    }
}

fn main() {}

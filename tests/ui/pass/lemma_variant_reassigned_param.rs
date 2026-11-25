//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The variant at a recursive call is compared with the parameter's value on entry, so a body that
// reassigns the parameter before the call still verifies when the argument is smaller.
#[thrust_macros::lemma]
#[thrust_macros::variant(n)]
#[thrust_macros::requires(n >= 0)]
#[thrust_macros::ensures(n >= 0)]
fn down(mut n: i64) {
    if n > 0 {
        n -= 1;
        down(n);
    }
}

fn main() {
    thrust_macros::proof!(down(3));
}

//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A lemma generic over a type without a `Model` bound of its own, whose variant does not read it.
#[thrust_macros::lemma]
#[thrust_macros::variant(n)]
#[thrust_macros::requires(n >= 0)]
#[thrust_macros::ensures(n >= 0)]
fn f<T: Copy>(x: T, n: i64) {
    if n > 0 {
        f(x, n - 1);
    }
}

fn main() {}

//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A macro in the variant reads the parameters at the entry values and at the call's arguments.
macro_rules! id {
    ($e:expr) => {
        $e
    };
}

#[thrust_macros::lemma]
#[thrust_macros::variant(m + id!(k) + 0 * k)]
#[thrust_macros::requires(m >= 0 && k == 0)]
#[thrust_macros::ensures(m >= 0)]
fn f(m: i64, k: i64) {
    if m > 0 {
        f(m - 1, k);
    }
}

fn main() {}

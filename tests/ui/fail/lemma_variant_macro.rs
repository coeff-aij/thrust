//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A macro in the variant reads the parameters: the variant is `m + k`, which does not decrease at
// `f(m - 1, 1 - m)` from the entry values.
macro_rules! id {
    ($e:expr) => {
        $e
    };
}

#[thrust_macros::lemma]
#[thrust_macros::variant(m + id!(k) + 0 * k)]
#[thrust_macros::ensures(false)]
fn f(m: i64, k: i64) {
    f(m - 1, 1 - m);
}

fn main() {}

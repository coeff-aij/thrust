//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The variant over a generic-typed argument is checked: `k + 1` does not decrease it.
#[thrust_macros::logic]
fn rest<T: thrust_models::Model>(_s: &[T], k: i64) -> i64 {
    k
}

#[thrust_macros::lemma]
#[thrust_macros::variant(rest::<T>(s, k))]
#[thrust_macros::requires(k >= 0)]
#[thrust_macros::ensures(false)]
fn up<T: thrust_models::Model>(s: &[T], k: i64) {
    up(s, k + 1);
}

fn main() {}

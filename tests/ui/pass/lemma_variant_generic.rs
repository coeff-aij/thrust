//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A variant over a generic-typed argument: the obligation is stated at the lemma's type
// parameter and instantiated at each recursive call.
#[thrust_macros::logic]
fn rest<T: thrust_models::Model>(_s: &[T], k: i64) -> i64 {
    k
}

#[thrust_macros::lemma]
#[thrust_macros::variant(rest::<T>(s, k))]
#[thrust_macros::requires(k >= 0)]
#[thrust_macros::ensures(k >= 0)]
fn down<T: thrust_models::Model>(s: &[T], k: i64) {
    if k > 0 {
        down(s, k - 1);
    }
}

fn main() {}

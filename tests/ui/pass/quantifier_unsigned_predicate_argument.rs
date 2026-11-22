//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A predicate's parameter is an argument of its calls, any term of its sort, so a variable its body
// equates to a part of it is not pinned: here the argument is `Some(-5)`, and the trusted formula
// holds over Rust values (no `u64` equals -5) only if `n` ranges over them.
use thrust_models::forall;

#[thrust_macros::predicate]
fn payload_nonneg(o: Option<u64>) -> bool {
    forall(|n| !(o == Some(n)) || n >= 0)
}

fn main() {
    let x = 0u64;
    let y = 0i64;
    thrust_macros::assume!(|x: u64| payload_nonneg(Some(x - 5)));
    assert!(y == 0);
}

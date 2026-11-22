//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A variable of a trusted `ensures` that its premise equates to a part of a program value keeps
// the model's range, so the postcondition applies to the payload of the result, which no fact
// says is `>= 0` without THRUST_INT_RANGE.
#[thrust::trusted]
#[thrust_macros::ensures(thrust_models::forall(|n| result == Some(n) ==> n < 10))]
fn small() -> Option<u64> {
    Some(3)
}

fn main() {
    if let Some(v) = small() {
        assert!(v < 10);
    }
}

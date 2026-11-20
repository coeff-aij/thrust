//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off

// A variable a quantifier binds at an unsigned type ranges over the integers `>= 0`, also
// without `THRUST_INT_RANGE`, so a checked `ensures` may rely on it.
use thrust_models::forall;

#[thrust_macros::ensures(forall(|i: usize| result <= i))]
fn least_index() -> usize {
    0
}

fn main() {
    let i = least_index();
    assert!(i == 0);
}

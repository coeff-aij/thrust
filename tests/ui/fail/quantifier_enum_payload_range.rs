//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_INT_RANGE=conversions THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A variable a quantifier binds at an enum type ranges over the values of the type: the integers
// in a variant's payload are in their range. Assuming a statement true of every such value then
// assumes nothing false.
use thrust_models::forall;

#[thrust_macros::ensures(forall(|o: Option<u8>| match o { Some(n) => n <= 255, None => true }))]
fn payloads_in_range() {}

fn main() {
    let x = 0i64;
    thrust_macros::assume!(|x: i64| x == 0
        && forall(|o: Option<u8>| match o { Some(n) => n <= 255, None => true }));
    assert!(x == 1);
}

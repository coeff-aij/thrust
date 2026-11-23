//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The predicates stating an enum's payload facts and a variable's guard are defined at a type
// parameter's sort and at each instance: a parameter of `Result<u64, T>` has `0 <=` of its `Ok`
// payload, and a variable of it compared as a whole value ranges over values with that fact.
use thrust_models::forall;
use thrust_models::model::UInt;
use thrust_models::Model;

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(match r { Ok(n) => n >= 0, Err(_) => true })]
fn ok_nonneg<T: Model>(r: Result<u64, T>) {}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(forall(|x: Result<UInt, <T as Model>::Ty>|
    x == x && match x { Ok(n) => n >= 1, Err(_) => true }))]
fn every_ok_nonneg<T: Model>() {}

fn main() {
    ok_nonneg::<i32>(Ok(1));
    ok_nonneg::<bool>(Err(true));
    every_ok_nonneg::<i32>();
    every_ok_nonneg::<bool>();
}

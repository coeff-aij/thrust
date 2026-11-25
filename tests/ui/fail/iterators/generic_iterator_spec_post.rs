//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The pass twin returning the item of a second step.
use thrust_models::Model;
#[thrust_macros::requires(thrust_macros::pre!(<I as Iterator>::next(it)))]
#[thrust_macros::ensures(thrust_macros::post!(<I as Iterator>::next(it), result))]
fn step<I>(it: &mut I) -> Option<I::Item>
where
    I: IteratorSpec,
    I::Item: Model,
{
    let _ = it.next();
    it.next()
}

fn main() {}

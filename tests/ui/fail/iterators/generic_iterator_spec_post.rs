//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The pass twin returning the item of a second step.

#[thrust_macros::requires(thrust_macros::pre!(<I as Iterator>::next(it)))]
#[thrust_macros::ensures(thrust_macros::post!(<I as Iterator>::next(it), result))]
fn step<I>(it: &mut I) -> Option<I::Item>
where
    I: IteratorSpec,
    I::Item: thrust_models::Model,
    I::Ty: PartialEq,
    <I::Item as thrust_models::Model>::Ty: PartialEq,
{
    let _ = it.next();
    it.next()
}

fn main() {}

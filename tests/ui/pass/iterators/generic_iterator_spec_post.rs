//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `post!` of `Iterator::next` at a type parameter `I: IteratorSpec` is the contract std.rs gives
// it there, which the call in the body takes too; `pre!` is its precondition, `inv` once
// `next` requires it.

#[thrust_macros::requires(thrust_macros::pre!(<I as Iterator>::next(it)))]
#[thrust_macros::ensures(thrust_macros::post!(<I as Iterator>::next(it), result))]
fn step<I>(it: &mut I) -> Option<I::Item>
where
    I: IteratorSpec,
    I::Item: thrust_models::Model,
    I::Ty: PartialEq,
    <I::Item as thrust_models::Model>::Ty: PartialEq,
{
    it.next()
}

fn main() {}

//@compile-flags: -C debug-assertions=off
// In a function analyzed once for all its type arguments, the closure takes an `I::Item`, which
// the context does not normalize; a `bool` is not one.

#[thrust_macros::requires(thrust_macros::pre!(g(b)))] //~ ERROR: `pre!` passes a value of type `bool` where the callee takes `<I as std::iter::Iterator>::Item`
#[thrust_macros::ensures(true)]
fn apply<I: Iterator, G: Fn(I::Item)>(i: I, g: G, b: bool)
where
    I::Item: thrust_models::Model,
{
}

fn main() {}

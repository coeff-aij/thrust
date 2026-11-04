//@compile-flags: -C debug-assertions=off
// A projection the context does not normalize is only itself: a `J::Item` is not an `I::Item`.

#[thrust_macros::requires(thrust_macros::pre!(g(j)))] //~ ERROR: `pre!` passes a value of type `<<J as std::iter::Iterator>::Item as thrust_models::Model>::Ty` where the callee takes `<I as std::iter::Iterator>::Item`
#[thrust_macros::ensures(true)]
fn apply<I: Iterator, J: Iterator, G: Fn(I::Item)>(i: I, g: G, j: J::Item)
where
    I::Item: thrust_models::Model,
    J::Item: thrust_models::Model,
{
}

fn main() {}

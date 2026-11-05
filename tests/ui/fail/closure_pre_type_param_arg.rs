//@compile-flags: -C debug-assertions=off
// In a function analyzed once for all its type arguments, the closure's bound `G: Fn(T)` is
// stated in the specification's own generics, so an `i32` is not a `T`.

#[thrust_macros::requires(thrust_macros::pre!(g(x)))] //~ ERROR: `pre!` passes a value of type `thrust_models::model::Int` where the callee takes `T`
#[thrust_macros::ensures(true)]
fn apply<T, G: Fn(T) -> i32>(g: G, x: i32, t: T) -> i32 {
    0
}

fn main() {}

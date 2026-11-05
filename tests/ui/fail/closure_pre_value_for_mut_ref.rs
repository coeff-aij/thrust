//@compile-flags: -C debug-assertions=off
// A `&mut i32` parameter takes the pair of a current and a final value, not an integer.

#[thrust::trusted]
#[thrust_macros::requires(thrust_macros::pre!(g(x)))] //~ ERROR: `pre!` passes a value of type `thrust_models::model::Int` where the callee takes `&mut i32`
#[thrust_macros::ensures(true)]
fn apply<G: FnMut(&mut i32)>(g: G, x: i32) {}

fn main() {
    apply(|r: &mut i32| *r += 1, 1);
}

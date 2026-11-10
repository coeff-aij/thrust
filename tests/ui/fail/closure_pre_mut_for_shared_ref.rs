//@compile-flags: -C debug-assertions=off
// A `&mut` argument is the pair of its current and final values, not the value a `&i32`
// parameter takes.

#[thrust::trusted]
#[thrust_macros::requires(thrust_macros::pre!(g(m)))] //~ ERROR: `pre!` passes a value of type `thrust_models::model::Mut<thrust_models::model::Int>` where the callee takes `&i32`
#[thrust_macros::ensures(true)]
fn apply<G: Fn(&i32)>(g: G, m: &mut i32) {}

fn main() {
    let mut v = 1;
    apply(|x: &i32| assert!(*x == 1), &mut v);
}

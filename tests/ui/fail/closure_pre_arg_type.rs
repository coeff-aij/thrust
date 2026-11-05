//@compile-flags: -C debug-assertions=off
// `pre!` passes each argument at the type the closure takes it. `true` is not an `i32`.

#[thrust::trusted]
#[thrust_macros::requires(thrust_macros::pre!(g(true)))] //~ ERROR: `pre!` passes a value of type `bool` where the callee takes `i32`
#[thrust_macros::ensures(true)]
fn apply<G: Fn(i32) -> i32>(g: G) -> i32 {
    0
}

fn main() {
    apply(|x: i32| x);
}

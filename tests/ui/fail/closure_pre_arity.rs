//@compile-flags: -C debug-assertions=off
// `pre!` of a closure takes as many arguments as the closure.

#[thrust::trusted]
#[thrust_macros::requires(thrust_macros::pre!(g(x, x)))] //~ ERROR: `pre!` arity mismatch: the callee takes 1 argument(s), given 2
#[thrust_macros::ensures(true)]
fn apply<G: Fn(i32) -> i32>(g: G, x: i32) -> i32 {
    g(x)
}

fn main() {
    apply(|x: i32| x, 1);
}

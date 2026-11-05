//@compile-flags: -C debug-assertions=off
// `post!` relates the arguments to a result of the type the closure returns. `true` is not an
// `i32`.

#[thrust::trusted]
#[thrust_macros::requires(thrust_macros::pre!(g(x)))]
#[thrust_macros::ensures(thrust_macros::post!(g(x), true))] //~ ERROR: `post!` passes a value of type `bool` where the callee returns `i32`
fn apply<G: Fn(i32) -> i32>(g: G, x: i32) -> i32 {
    g(x)
}

fn main() {
    apply(|x: i32| x, 1);
}

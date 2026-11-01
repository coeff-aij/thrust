//@check-pass
//@compile-flags: -C debug-assertions=off
// `G` is instantiated with a reference to a closure, which calls the closure: `pre!` and
// `post!` of `g` are those of the closure at the state `g` points to.

#[thrust::trusted]
#[thrust_macros::requires(thrust_macros::pre!(g(x)))]
#[thrust_macros::ensures(thrust_macros::post!(g(x), result))]
fn apply<G: Fn(i32) -> i32>(g: G, x: i32) -> i32 {
    g(x)
}

fn main() {
    let k = 3;
    let a = move |x: i32| {
        assert!(x > k);
        x + k
    };
    assert!(apply(&a, 4) == 7);
}

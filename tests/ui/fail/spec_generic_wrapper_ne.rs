//@compile-flags: -C debug-assertions=off -A unused-variables

// A generic wrapper whose model is itself holds a `&str` at `W<&str>`: the contract's `!=`,
// checked at the instance it is used at, would be false of every pair there.
#[derive(Clone, Copy)]
struct W<T>(T);
impl<T> thrust_models::Model for W<T> {
    type Ty = W<T>;
}

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result != a)] //~ ERROR: cannot compare values of `W<&str>`
fn other<T: Copy>(a: W<T>, b: W<T>) -> W<T> {
    b
}

fn main() {
    let _ = other(W("x"), W("y"));
    assert!(1 == 2);
}

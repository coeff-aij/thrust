//@compile-flags: -C debug-assertions=off -A unused-variables

// The `requires` side: `a == b` at `W<&str>` would hold of any two values.
#[derive(Clone, Copy)]
struct W<T>(T);
impl<T> thrust_models::Model for W<T> {
    type Ty = W<T>;
}

#[thrust::trusted]
#[thrust_macros::requires(a == b)] //~ ERROR: cannot compare values of `W<&str>`
#[thrust_macros::ensures(true)]
fn need_same<T: Copy>(a: W<T>, b: W<T>) {}

fn main() {
    need_same(W("x"), W("y"));
}

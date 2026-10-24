//@compile-flags: -C debug-assertions=off -A unused-variables

// The same contract used through a generic caller, instantiated at `&str` there.
#[derive(Clone, Copy)]
struct W<T>(T);
impl<T> thrust_models::Model for W<T> {
    type Ty = W<T>;
}

#[thrust::trusted]
#[thrust_macros::requires(a == b)] //~ ERROR: cannot compare values of `W<&str>`
#[thrust_macros::ensures(true)]
fn need_same<T: Copy>(a: W<T>, b: W<T>) {}

fn g<U: Copy>(x: W<U>, y: W<U>) {
    need_same(x, y)
}

fn main() {
    g(W("x"), W("y"));
}

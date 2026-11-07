//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `outer`'s body is analyzed at `caller`'s arguments, where the `Fn` bound of `outer`'s `H` has
// to be read at those arguments to name `caller`'s parameters; `H` declared before `T` is what
// makes `H` share its index with `caller`'s own `H`.
#[thrust::trusted]
#[thrust_macros::requires(thrust_macros::pre!(g(t)))]
#[thrust_macros::ensures(true)]
fn apply<T, G: Fn(T)>(g: G, t: T) {
    g(t)
}

#[thrust_macros::requires(thrust_macros::pre!(h(t)))]
#[thrust_macros::ensures(true)]
fn outer<H: Fn(T), T>(h: H, t: T) {
    apply(&h, t)
}

#[thrust_macros::requires(thrust_macros::pre!(h(1)))]
#[thrust_macros::ensures(true)]
fn caller<H: Fn(i64)>(h: H) {
    outer(h, 2i64)
}

fn main() {
    caller(|x: i64| assert!(x < 2));
}

//@compile-flags: -C debug-assertions=off
// A closure that a trusted body runs without an analyzed call handing it over stops, though
// another call hands the same closure over with a stated `pre!`.

#[thrust::trusted]
#[thrust_macros::requires(thrust_macros::pre!(f(x)))]
#[thrust_macros::ensures(true)]
fn apply_pre<F: Fn(i32)>(f: F, x: i32) {
    f(x)
}

fn mk() -> impl Fn(i32) {
    |x: i32| assert!(x > 0) //~ ERROR: without an analyzed call handing it over
}

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn t() {
    let f = mk();
    f(0)
}

fn main() {
    apply_pre(mk(), 1);
    t()
}

//@compile-flags: -C debug-assertions=off
// A closure that an analyzed function returns to a trusted body, which may call it with any
// argument, stops, though another call hands the same closure over with a stated `pre!`.

#[thrust::trusted]
#[thrust_macros::requires(thrust_macros::pre!(f(x)))]
#[thrust_macros::ensures(true)]
fn apply_pre<F: Fn(i32)>(f: F, x: i32) {
    f(x)
}

fn mk() -> impl Fn(i32) { //~ ERROR: which Thrust does not analyze
    |x: i32| assert!(x > 0)
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

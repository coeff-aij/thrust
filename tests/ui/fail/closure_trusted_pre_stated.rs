//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
// A trusted function that states `pre!` of its closure asks only that of its caller.

#[thrust::trusted]
#[thrust_macros::requires(thrust_macros::pre!(f(x)))]
#[thrust_macros::ensures(true)]
fn apply_pre<F: Fn(i32)>(f: F, x: i32) {
    f(x)
}

fn main() {
    apply_pre(|x: i32| assert!(x > 0), 0);
}

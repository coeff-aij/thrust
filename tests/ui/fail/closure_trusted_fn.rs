//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
// A closure handed to a trusted function whose contract states no `pre!` of it must accept
// every argument.

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn apply<F: Fn(i32)>(f: F, x: i32) {
    f(x)
}

fn main() {
    apply(|x: i32| assert!(x > 0), 0);
}

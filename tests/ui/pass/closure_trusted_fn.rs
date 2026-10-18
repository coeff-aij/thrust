//@check-pass
//@compile-flags: -C debug-assertions=off
// The twin of `fail/closure_trusted_fn.rs`: the closure accepts every argument, given its
// capture as it is at the call.

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn apply<F: Fn(i32)>(f: F, x: i32) {
    f(x)
}

fn main() {
    let y = 5;
    apply(move |_: i32| assert!(y > 0), 0);
}

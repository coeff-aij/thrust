//@check-pass
//@compile-flags: -C debug-assertions=off
// A trusted function whose `requires` does not state the `pre!` of the closure it calls asks
// nothing of the closure (D59 (b), as in Creusot): its contract is wrong if the closure needs
// more, which is its author's responsibility. The closure's precondition comes from the calls
// Thrust analyzes, here `f(1)`.

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn apply<F: Fn(i32)>(f: F, x: i32) {
    f(x)
}

fn main() {
    let f = |x: i32| assert!(x > 0);
    apply(f, 0);
    f(1);
}

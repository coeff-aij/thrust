//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `counter.rs`'s closure written in a generic function and called at a concrete type argument:
// the relation over its owned counter there is the one its body, analyzed at that argument,
// constrains.

#[thrust::callable]
fn mk<T>(_t: T) -> impl FnMut() -> i64 {
    let mut n: i64 = 0;
    thrust_macros::closure!(
        captures(n: &mut i64),
        requires(true),
        ensures(!n == *n + 1 && result == !n),
        move || -> i64 {
            n += 1;
            n
        },
    )
}

fn main() {
    let mut c = mk(0i64);
    let a = c();
    let b = c();
    assert!(b == a + 1);
}

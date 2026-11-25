//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `generic_owner.rs` with the closure called from a generic function, at that function's type
// parameter.

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

fn twice<U>(u: U) {
    let mut c = mk(u);
    let a = c();
    let b = c();
    assert!(b == a + 1);
}

fn main() {
    twice(0i64);
}

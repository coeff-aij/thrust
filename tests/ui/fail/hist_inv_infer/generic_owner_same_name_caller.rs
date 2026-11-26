//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `generic_owner_generic_caller.rs` with a capture of the type parameter, called from a caller
// whose type parameter has the same name: the closure's type there is the one at its own
// parameters, but the sort of that capture is the caller's.

#[thrust::callable]
fn mk<T>(t: T) -> impl FnMut() -> i64 {
    let mut n: i64 = 0;
    thrust_macros::closure!(
        captures(n: &mut i64),
        requires(true),
        ensures(!n == *n + 1 && result == !n),
        move || -> i64 {
            let _r = &t;
            n += 1;
            n
        },
    )
}

#[thrust::callable]
fn twice<T>(u: T) {
    let mut c = mk(u);
    let a = c();
    let b = c();
    assert!(b == a);
}

fn main() {
    twice(0i64);
}

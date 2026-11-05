//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `check`'s `hist_inv` clause relates its states through `P`'s. At an argument without captures,
// whose contract is left to inference so that `wrap` is analyzed again at it, `check`'s state
// has a single value, which stands for its receiver in that clause.
#[thrust_macros::context]
fn wrap<P: FnMut() -> bool>(mut p: P) -> bool {
    let mut check = thrust_macros::closure!(
        captures(p: &mut P),
        hist_inv(thrust_macros::hist_inv!(*p, !p)),
        move || -> bool { p() },
    );
    check()
}

fn main() {
    assert!(wrap(|| -> bool { true }));
}

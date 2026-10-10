//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A derived `==` instantiated at `&mut` compares the current values, so the generic
// `PartialEq` spec, which compares models, does not apply to it.

#[derive(PartialEq)]
struct S<T> {
    x: T,
}

fn main() {
    let mut a = 1;
    let mut b = 1;
    let sa = S { x: &mut a };
    let sb = S { x: &mut b };
    let r = sa == sb;
    *sa.x = 5;
    assert!(!r);
}

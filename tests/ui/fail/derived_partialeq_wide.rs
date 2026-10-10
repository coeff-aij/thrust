//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The derived `eq` of a struct with many fields is the equality of the models, without the
// `&&` chain of its body.

#[derive(Clone, Copy, PartialEq, Eq)]
struct Wide {
    f0: u32,
    f1: u32,
    f2: u32,
    f3: u32,
    f4: u32,
    f5: u32,
    f6: u32,
    f7: u32,
    f8: u32,
    f9: u32,
    f10: u32,
    f11: u32,
    f12: u32,
    f13: u32,
    f14: u32,
    f15: u32,
    f16: u32,
    f17: u32,
}

fn main() {
    let a = Wide { f0: 0, f1: 1, f2: 2, f3: 3, f4: 4, f5: 5, f6: 6, f7: 7, f8: 8, f9: 9, f10: 10, f11: 11, f12: 12, f13: 13, f14: 14, f15: 15, f16: 16, f17: 17 };
    let b = a;
    let c = Wide { f17: 0, ..a };
    assert!(a == b);
    assert!(a == c);
}

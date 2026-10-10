//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A type whose `PartialOrd` is derived and that has no `PartialOrdSpec` impl is ordered by its
// fields' orders, lexicographically, and a fieldless enum by its discriminants; `<`, `cmp` and
// `max` are specified through that order.

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct Align {
    pow2: u8,
}

impl thrust_models::Model for Align {
    type Ty = Self;
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct Version {
    major: u32,
    minor: i64,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Integer {
    I8 = 3,
    I16 = 1,
    I32,
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result.pow2 >= a.pow2 && result.pow2 >= b.pow2)]
fn larger(a: Align, b: Align) -> Align {
    a.max(b)
}

fn main() {
    let v = Version { major: 1, minor: 9 };
    let w = Version { major: 2, minor: -5 };
    let x = Version { major: 1, minor: 10 };
    assert!(v < w);
    assert!(v < x);
    assert!(v.cmp(&x) == std::cmp::Ordering::Less);
    assert!(v.max(x).minor == 9);
    assert!(Integer::I16 < Integer::I32);
    assert!(Integer::I32 < Integer::I8);
}

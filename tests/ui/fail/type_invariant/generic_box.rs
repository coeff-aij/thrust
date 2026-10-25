//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `g` is verified over `T` and calls `bump` at `T`, where its contract has no invariant. At `C`
// its body is analyzed again, where the call runs `C::bump`, which assumes the invariant of the
// value inside the `Box`, which the contract of `g` does not require.

#[thrust_macros::context]
trait Counter {
    #[thrust_macros::ensures(result <= 100)]
    fn bump(&mut self) -> u32;
}

struct C {
    n: u32,
}

impl thrust_models::Model for C {
    type Ty = Self;
}

#[thrust_macros::context]
impl Invariant for C {
    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        self.n % 2 == 0
    }
}

// Meets the trait's contract only under the invariant.
impl Counter for C {
    fn bump(&mut self) -> u32 {
        if self.n % 2 == 1 { 1000 } else { 0 }
    }
}

#[thrust_macros::ensures(result <= 100)]
fn g<T: Counter>(mut x: Box<T>) -> u32 {
    x.bump()
}

fn main() {
    let r = g(Box::new(C { n: 1 }));
    assert!(r <= 100);
}

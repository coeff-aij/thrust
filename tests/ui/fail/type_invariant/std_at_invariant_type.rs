//@error-in-other-file: would promise the invariant
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// std's `Option::unwrap` is not analyzed, and its contract at `C` would promise the invariant of
// the result, which the `Some` does not have: std code at a type with an invariant is rejected.
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

fn main() {
    let c = Some(C { n: 1 }).unwrap();
    assert!(c.n % 2 == 0);
}

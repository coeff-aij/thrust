//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A generic impl calls `bump` on its field at `T`. At `W<C>` its body is analyzed again, where the
// call runs `C::bump`, which assumes the invariant of the field.

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

struct W<T>(T);

impl<T: thrust_models::Model> thrust_models::Model for W<T> {
    type Ty = T::Ty;
}

impl<T: Counter> Counter for W<T> {
    fn bump(&mut self) -> u32 {
        self.0.bump()
    }
}

fn main() {
    let mut w = W(C { n: 1 });
    let r = w.bump();
    assert!(r <= 100);
}

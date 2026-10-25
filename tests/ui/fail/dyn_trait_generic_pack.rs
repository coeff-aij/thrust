//@error-in-other-file: a value whose type holds a type parameter
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// Packing at a type parameter is rejected: `T`'s invariant, which `C`'s methods assume at the
// instance, is not known there, so it could not be required.

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

impl Counter for C {
    fn bump(&mut self) -> u32 {
        if self.n % 2 == 1 {
            1000
        } else {
            0
        }
    }
}

fn pack<T: Counter + 'static>(x: Box<T>) -> Box<dyn Counter> {
    x
}

fn main() {
    let mut d = pack(Box::new(C { n: 2 }));
    let r = d.bump();
    assert!(r <= 100);
}

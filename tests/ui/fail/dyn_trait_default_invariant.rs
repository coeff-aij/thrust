//@error-in-other-file: has no contract on the trait
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A default body that breaks `C`'s invariant through `get`, whose `&mut self` borrow outlives the
// call, would leave the invariant broken for `bump`; `get` has no contract, and the default body
// analyzed at the trait object calls it through it, which is rejected.

#[thrust_macros::context]
trait Counter {
    fn get(&mut self) -> &mut u32;

    #[thrust_macros::ensures(true)]
    fn reset(&mut self) {
        *self.get() = 1;
    }

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
    fn get(&mut self) -> &mut u32 {
        &mut self.n
    }

    fn bump(&mut self) -> u32 {
        if self.n % 2 == 1 {
            1000
        } else {
            0
        }
    }
}

fn main() {
    let mut c = C { n: 2 };
    let d: &mut dyn Counter = &mut c;
    d.reset();
    let r = d.bump();
    assert!(r <= 100);
}

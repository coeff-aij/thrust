//@error-in-other-file: its invariant is not ensured after
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// As `dyn_trait_invariant_escape`, with a contract of the impl's own on `get`, which does not
// ensure `C`'s invariant either (its borrow outlives the call), so packing `C` is rejected.

#[thrust_macros::context]
trait Counter {
    #[thrust_macros::ensures(true)]
    fn get(&mut self) -> &mut u32;

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

#[thrust_macros::context]
impl Counter for C {
    #[thrust_macros::ensures(true)]
    fn get(&mut self) -> &mut u32 {
        &mut self.n
    }

    fn bump(&mut self) -> u32 {
        if self.n % 2 == 1 {
            100
        } else {
            0
        }
    }
}

fn main() {
    let mut c = C { n: 2 };
    let d: &mut dyn Counter = &mut c;
    *d.get() = 1;
    let r = d.bump();
    assert!(r <= 100);
}

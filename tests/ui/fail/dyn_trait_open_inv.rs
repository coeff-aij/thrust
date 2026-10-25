//@error-in-other-file: its invariant is not ensured after
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A trait method whose `&mut self` is `#[thrust::open_inv]` does not ensure `C`'s invariant of
// the final value, which later calls through the trait object would assume, so packing `C` is
// rejected.

#[thrust_macros::context]
trait Counter {
    #[thrust_macros::ensures(result <= 100)]
    fn bump(#[thrust::open_inv] &mut self) -> u32;
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

fn main() {
    let mut c = C { n: 2 };
    let d: &mut dyn Counter = &mut c;
    let r = d.bump();
    assert!(r <= 100);
}

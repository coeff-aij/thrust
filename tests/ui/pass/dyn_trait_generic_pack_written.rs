//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// As `dyn_trait_generic_pack`, with a written contract on `pack`, which is verified once over `T`
// (where `T` has no invariant to require) and also at `T = C`, where packing requires `C`'s.

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

#[thrust::callable]
fn pack<'a, T: Counter + 'a>(x: &'a mut T) -> &'a mut dyn Counter {
    x
}

fn main() {
    let mut c = C { n: 2 };
    let d = pack(&mut c);
    let r = d.bump();
    assert!(r <= 100);
}

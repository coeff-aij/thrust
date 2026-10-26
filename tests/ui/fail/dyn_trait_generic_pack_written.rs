//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `pack`, with a written contract, is verified once over `T` and also at `T = C`. The caller
// passes a valid `C`; `spoil`, whose receiver is `open_inv` and which is not in the vtable,
// breaks `C`'s invariant inside `pack`, so only the requirement of packing at `T = C` refutes
// it (`bump` would return 1000).

#[thrust_macros::context]
trait Counter {
    #[thrust_macros::ensures(result <= 100)]
    fn bump(&mut self) -> u32;

    #[thrust_macros::ensures(true)]
    fn spoil(#[thrust::open_inv] &mut self)
    where
        Self: Sized;
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
    fn spoil(&mut self) {
        self.n = 1;
    }

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
    x.spoil();
    x
}

fn main() {
    let mut c = C { n: 2 };
    let d = pack(&mut c);
    let r = d.bump();
    assert!(r <= 100);
}

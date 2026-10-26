//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `pack` is analyzed at `T = C`, where packing requires `C`'s invariant, which `C { n: 1 }` breaks:
// `bump` would return 1000.

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
    let mut d = pack(Box::new(C { n: 1 }));
    let r = d.bump();
    assert!(r <= 100);
}

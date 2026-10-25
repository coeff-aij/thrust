//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A method whose `&mut self` borrow outlives the call (`get` returns a `&mut` into it) may be in
// the vtable of a type without an invariant.

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

impl Counter for C {
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

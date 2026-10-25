//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The default `reset` writes through `get`, which `C` overrides to lend its field, so at `C` it
// breaks the invariant; `get`'s contract is not the default's but `C::get`'s, inferred from its
// body.
#[thrust_macros::context]
trait Counter {
    fn get(&mut self) -> Option<&mut u32> {
        None
    }

    #[thrust_macros::ensures(true)]
    fn reset(&mut self) {
        if let Some(r) = self.get() {
            *r = 1;
        }
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
    fn get(&mut self) -> Option<&mut u32> {
        None
    }

    fn bump(&mut self) -> u32 {
        if self.n % 2 == 1 { 1000 } else { 0 }
    }
}

fn main() {
    let mut c = C { n: 2 };
    c.reset();
    let r = c.bump();
    assert!(r <= 100);
}

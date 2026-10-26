//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The twin of `fail/dyn_trait_model_supertrait.rs`: a trait without a `Model` supertrait.

#[derive(PartialEq)]
struct C {
    n: u32,
}

impl thrust_models::Model for C {
    type Ty = Self;
}

#[thrust_macros::context]
trait Tick {
    #[thrust_macros::ensures(result >= 1)]
    fn tick(&mut self) -> u32;
}

impl Tick for C {
    fn tick(&mut self) -> u32 {
        if self.n < 100 {
            self.n += 1;
        } else {
            self.n = 0;
        }
        1
    }
}

fn f(c: &mut dyn Tick) {
    let r = c.tick();
    assert!(r >= 1);
}

fn main() {
    let mut c = C { n: 0 };
    f(&mut c);
}

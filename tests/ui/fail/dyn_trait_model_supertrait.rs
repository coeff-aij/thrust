//@error-in-other-file: as a supertrait are not supported
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A `Model` supertrait fixes the receiver's model to `C` in the trait's contracts, while a trait
// object's model is opaque, so a trait object of such a trait is rejected.

#[derive(PartialEq)]
struct C {
    n: u32,
}

impl thrust_models::Model for C {
    type Ty = Self;
}

#[thrust_macros::context]
trait Tick: thrust_models::Model<Ty = C> {
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

//@error-in-other-file: its contract mentions `self` or `Self`
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A contract about the receiver is rejected at a call through `dyn`: the trait object's model is
// single-valued, so `*self != !self` would be false there and the code after the call vacuous.

#[thrust_macros::context]
trait Tick {
    #[thrust_macros::ensures(result >= 1 && *self != !self)]
    fn tick(&mut self) -> u32;
}

#[derive(PartialEq)]
struct C {
    n: u32,
}

impl thrust_models::Model for C {
    type Ty = Self;
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

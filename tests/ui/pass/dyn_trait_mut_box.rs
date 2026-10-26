//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// Calls through `&mut dyn Counter` and `Box<dyn Counter>`, to an impl whose model is not unit.

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

impl Counter for C {
    fn bump(&mut self) -> u32 {
        if self.n < 100 {
            self.n += 1;
            self.n
        } else {
            100
        }
    }
}

#[thrust_macros::ensures(result <= 100)]
fn via_mut(c: &mut dyn Counter) -> u32 {
    c.bump()
}

#[thrust_macros::ensures(result <= 100)]
fn via_box(mut c: Box<dyn Counter>) -> u32 {
    c.bump()
}

fn main() {
    let mut c = C { n: 0 };
    let a = via_mut(&mut c);
    let b = via_box(Box::new(C { n: 5 }));
    assert!(a <= 100 && b <= 100);
}

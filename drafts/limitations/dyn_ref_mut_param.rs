// A `&mut C` parameter, `C` with an invariant, passed on as `&mut dyn Counter`.
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
        if self.n % 2 == 1 { 1000 } else { 0 }
    }
}

fn via_dyn(d: &mut dyn Counter) -> u32 {
    d.bump()
}

#[thrust_macros::ensures(result <= 100)]
fn f(x: &mut C) -> u32 {
    via_dyn(x)
}

fn main() {
    let mut c = C { n: 2 };
    assert!(f(&mut c) <= 100);
}

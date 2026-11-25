// A generic function with a written contract packs a `Box<T>`; called at a type with an invariant.
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

#[thrust::callable]
fn pack<T: Counter + 'static>(x: Box<T>) -> Box<dyn Counter> {
    x
}

fn main() {
    let mut d = pack(Box::new(C { n: 2 }));
    assert!(d.bump() <= 100);
}

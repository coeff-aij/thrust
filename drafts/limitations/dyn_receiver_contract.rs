// A contract that mentions the receiver, called through `&mut dyn Tick`.
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
        if self.n < 100 { self.n += 1; } else { self.n = 0; }
        1
    }
}

fn f(c: &mut dyn Tick) {
    assert!(c.tick() >= 1);
}

fn main() {
    let mut c = C { n: 0 };
    f(&mut c);
}

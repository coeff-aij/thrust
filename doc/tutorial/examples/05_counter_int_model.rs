use thrust_models::model::Int;
use thrust_models::Model;

#[thrust_macros::context]
trait Counter: Model {
    #[thrust_macros::logic]
    fn count(self) -> Int;

    #[thrust_macros::law]
    #[thrust_macros::ensures(Self::count(*c) >= 0)]
    fn count_nonneg(c: &Self);

    #[thrust_macros::ensures(Self::count(!self) == Self::count(*self) + 1)]
    fn tick(&mut self);
}

#[thrust_macros::context]
#[thrust_macros::ensures(C::count(!c) == C::count(*c) + 2)]
#[thrust_macros::ensures(C::count(!c) >= 2)]
fn tick_twice<C: Counter>(c: &mut C) {
    c.tick();
    c.tick();
}

struct Clicks {
    n: u64,
}

impl Model for Clicks {
    type Ty = (Int,);
}

#[thrust_macros::context]
impl Counter for Clicks {
    #[thrust_macros::logic]
    fn count(self) -> Int {
        self.0
    }

    fn count_nonneg(c: &Clicks) {}

    fn tick(&mut self) {
        self.n += 1;
    }
}

fn main() {
    let mut c = Clicks { n: 0 };
    tick_twice(&mut c);
    assert!(c.n == 2);
}

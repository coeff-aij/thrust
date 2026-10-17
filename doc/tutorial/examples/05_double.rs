#[derive(PartialEq)]
struct Meter {
    m: i64,
}

impl thrust_models::Model for Meter {
    type Ty = Self;
}

#[thrust_macros::context]
trait Double {
    #[thrust_macros::predicate]
    fn is_double(self, doubled: Self) -> bool;

    #[thrust_macros::ensures(Self::is_double(*self, !self))]
    fn double(&mut self);
}

#[thrust_macros::context]
impl Double for Meter {
    #[thrust_macros::predicate]
    fn is_double(self, doubled: Self) -> bool {
        self.m * 2 == doubled.m
    }

    fn double(&mut self) {
        self.m += self.m;
    }
}

fn main() {
    let mut a = Meter { m: 3 };
    a.double();
    assert!(a.m == 6);
}

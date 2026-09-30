//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// `<=` compares through the derived `partial_cmp`, as `<` does.
#[derive(PartialEq, PartialOrd, thrust_macros::Model)]
struct P {
    a: i64,
    b: i64,
}

// The derived order compares the fields in order.
#[thrust_macros::context]
impl PartialOrdSpec for P {
    #[thrust_macros::predicate]
    fn compares(self, other: Self, ord: Option<std::cmp::Ordering>) -> bool {
        (self.a < other.a && ord == Some(std::cmp::Ordering::Less))
            || (self.a > other.a && ord == Some(std::cmp::Ordering::Greater))
            || (self.a == other.a
                && ((self.b < other.b && ord == Some(std::cmp::Ordering::Less))
                    || (self.b == other.b && ord == Some(std::cmp::Ordering::Equal))
                    || (self.b > other.b && ord == Some(std::cmp::Ordering::Greater))))
    }

    fn compares_functional(
        a: &Self,
        b: &Self,
        x: Option<std::cmp::Ordering>,
        y: Option<std::cmp::Ordering>,
    ) {
    }
}

#[thrust_macros::requires(x == PModel { a: 1, b: 5 } && y == PModel { a: 1, b: 4 })]
#[thrust_macros::ensures(true)]
fn check(x: P, y: P) {
    assert!(x <= y);
}

fn main() {
    check(P { a: 1, b: 5 }, P { a: 1, b: 4 });
}

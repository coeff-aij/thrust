//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_VERIFY_ONLY=h THRUST_SOLVER=tests/thrust-pcsat-wrapper

// Only `h` is selected; the generic `number` outside the selection is analyzed, and its spec bound
// holds at the instance `h` makes: `Good` implements `IteratorSpec`.

#[derive(PartialEq)]
struct Good;

impl thrust_models::Model for Good {
    type Ty = Self;
}

impl Iterator for Good {
    type Item = i64;

    fn next(&mut self) -> Option<i64> {
        None
    }
}

#[thrust_macros::context]
impl IteratorSpec for Good {
    #[thrust_macros::predicate]
    fn inv(self) -> bool {
        true
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Vec<i64>, o: Self) -> bool {
        visited.len() == 0
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        *self == !self
    }

    fn produces_refl(a: &Self) {}

    fn produces_trans(
        a: &Self,
        ab: thrust_models::model::Seq<<Self::Item as thrust_models::Model>::Ty>,
        b: &Self,
        bc: thrust_models::model::Seq<<Self::Item as thrust_models::Model>::Ty>,
        c: &Self,
    ) {
    }
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn number<J: Iterator<Item = i64>>(j: J) {
    let _ = j.enumerate();
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn h() {
    number(Good);
}

fn main() {}

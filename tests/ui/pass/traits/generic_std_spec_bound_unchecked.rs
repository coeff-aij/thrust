//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The spec bound is reached through `enumerate`, which steps nothing: `Vec::from_iter(j)` requires
// `inv` of the iterator `j`'s `into_iter` makes, as Creusot requires the type invariant of the
// iterator `extend` and `collect` step, and a contract over `J: IntoIterator` cannot state it.
use thrust_models::{Model, model::Seq};
#[derive(PartialEq)]
struct Good;

impl Model for Good {
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
        ab: Seq<<Self::Item as Model>::Ty>,
        b: &Self,
        bc: Seq<<Self::Item as Model>::Ty>,
        c: &Self,
    ) {
    }
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn number<J: Iterator<Item = i64>>(j: J) {
    let _ = j.enumerate();
}

fn main() {
    number(Good);
}

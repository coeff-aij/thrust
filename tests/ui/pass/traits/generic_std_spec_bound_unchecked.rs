//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:9799dfd7b

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

#[thrust_macros::context]
impl IntoIteratorSpec for Good {
    #[thrust_macros::predicate]
    fn into_iter_is(self, it: Self) -> bool {
        self == it
    }
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn collect<J: IntoIterator<Item = i64>>(j: J) -> Vec<i64> {
    Vec::from_iter(j)
}

fn main() {
    let v = collect(Good);
    assert!(v.len() >= 0);
}

//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:804d76744

// The iterator's `next` panics. `Vec::from_iter` has to assume it may: the local `next` is checked
// against `requires(true)`.

#[derive(PartialEq)]
struct Bad(i64);

impl thrust_models::Model for Bad {
    type Ty = Bad;
}

impl Iterator for Bad {
    type Item = i64;

    fn next(&mut self) -> Option<i64> {
        assert!(self.0 > 100);
        None
    }
}

#[thrust_macros::context]
impl IteratorSpec for Bad {
    #[thrust_macros::predicate]
    fn inv(self) -> bool {
        true
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Vec<i64>, o: Self) -> bool {
        visited.len() == 0 && self == o
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        true
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
impl IntoIteratorSpec for Bad {
    #[thrust_macros::predicate]
    fn into_iter_is(self, it: Self) -> bool {
        self == it
    }
}

fn main() {
    let _v: Vec<i64> = Vec::from_iter(Bad(1));
}

//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A generic impl method's spec bound, reached through a trait method called at a type parameter,
// holds at the instance: `Good` implements `IteratorSpec`.

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

struct W<J>(Option<J>);

impl<J: thrust_models::Model> thrust_models::Model for W<J> {
    type Ty = Option<<J as thrust_models::Model>::Ty>;
}

impl<J: Iterator<Item = i64> + thrust_models::Model> Iterator for W<J> {
    type Item = i64;

    fn next(&mut self) -> Option<i64> {
        if let Some(j) = self.0.take() {
            let _ = j.enumerate();
        }
        None
    }
}

#[thrust_macros::context]
impl<J: Iterator<Item = i64> + thrust_models::Model> IteratorSpec for W<J> {
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
        true
    }

    fn produces_refl(a: &Self) {}

    fn produces_trans(
        a: &Self,
        ab: thrust_models::model::Seq<thrust_models::model::Int>,
        b: &Self,
        bc: thrust_models::model::Seq<thrust_models::model::Int>,
        c: &Self,
    ) {
    }
}

#[thrust_macros::context]
#[thrust_macros::requires(I::inv(*it))]
#[thrust_macros::ensures(true)]
fn step<I: IteratorSpec>(it: &mut I)
where
    I::Item: thrust_models::Model,
{
    let _ = it.next();
}

fn main() {
    let mut w = W(Some(Good));
    step(&mut w);
}

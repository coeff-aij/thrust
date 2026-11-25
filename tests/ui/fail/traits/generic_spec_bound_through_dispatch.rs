//@error-in-other-file: spec bound not satisfied
// Rejected, not Unsat. `W<J>::next` is verified once, generically; its call `j.enumerate()`
// assumes the spec bound `J: IteratorSpec`. `step` reaches `W<Bad>::next` only through
// `Iterator::next` at its type parameter `I`, so the bound is checked at the instance the call
// resolves to, `J = Bad`, which has no `IteratorSpec` impl. Without that check it verified.
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
use thrust_models::{Model, model::{Int, Seq}};
struct Bad;

impl Model for Bad {
    type Ty = Self;
}

#[thrust_macros::context]
impl Bad {
    #[thrust_macros::requires(false)]
    fn next_bad(&mut self) -> Option<i64> {
        panic!()
    }

    #[thrust::extern_spec_fn]
    #[thrust_macros::requires(false)]
    fn _extern_spec_next(it: &mut Bad) -> Option<i64> {
        <Bad as Iterator>::next(it)
    }
}

impl Iterator for Bad {
    type Item = i64;

    fn next(&mut self) -> Option<i64> {
        self.next_bad()
    }
}

struct W<J>(Option<J>);

impl<J: Model> Model for W<J> {
    type Ty = Option<<J as Model>::Ty>;
}

impl<J: Iterator<Item = i64> + Model> Iterator for W<J> {
    type Item = i64;

    fn next(&mut self) -> Option<i64> {
        if let Some(j) = self.0.take() {
            let _ = j.enumerate();
        }
        None
    }
}

#[thrust_macros::context]
impl<J: Iterator<Item = i64> + Model> IteratorSpec for W<J> {
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
        ab: Seq<Int>,
        b: &Self,
        bc: Seq<Int>,
        c: &Self,
    ) {
    }
}

#[thrust_macros::context]
#[thrust_macros::requires(I::inv(*it))]
#[thrust_macros::ensures(true)]
fn step<I: IteratorSpec>(it: &mut I)
where
    I::Item: Model,
{
    let _ = it.next();
}

fn main() {
    let mut w = W(Some(Bad));
    step(&mut w);
}

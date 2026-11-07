//@error-in-other-file: Unsat
//@compile-flags: --crate-type=lib -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120
use thrust_models::model::{Int, Mut, Seq};
use thrust_models::{exists, forall, Ghost, Model};

// Creusot's `Skip` (3620de437, `examples/iterators/04_skip.rs`): `next` drains up to `n` items in
// a loop whose invariant carries the skipped prefix, then answers with the inner iterator's result.

#[path = "../../pass/creusot/common.rs"]
mod common;
use common::Iterator;

// std.rs has no specification of `std::mem::take`, which `Skip::next` calls at `usize`.
#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == *dest && !dest == 0)]
fn _extern_spec_mem_take_usize(dest: &mut usize) -> usize {
    std::mem::take(dest)
}

pub struct Skip<I: Iterator>
where
    <I as Iterator>::Item: Model,
{
    pub iter: I,
    pub n: usize,
}

impl<I: Iterator> Model for Skip<I>
where
    <I as Iterator>::Item: Model,
{
    type Ty = (<I as Model>::Ty, <usize as Model>::Ty);
}

#[thrust_macros::context]
impl<I> Iterator for Skip<I>
where
    I: Iterator,
    <I as Iterator>::Item: Model,
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty>,
    <<I as Iterator>::Item as Model>::Ty: Model<Ty = <<I as Iterator>::Item as Model>::Ty>,
    <Skip<I> as Model>::Ty: Model<Ty = <Skip<I> as Model>::Ty>,
{
    type Item = I::Item;

    fn next(&mut self) -> Option<I::Item> {
        let s = self;
        let mut n = std::mem::take(&mut s.n);
        let mut skipped = thrust_macros::ghost!(|| -> Seq<<I::Item as Model>::Ty> { Seq::empty() });

        // Creusot's `old_self` is the entry value of `self`, which an invariant names as `self`
        // (`FnParam`), so the current value is `s`. Creusot's first two invariants, and what its
        // prophecies and the type invariant give: the final value of `self`, its zero `n` and the
        // inner iterator's invariant. Thrust has no `resolve`, Creusot's third invariant.
        loop {
            thrust_macros::invariant!(
                |s: &mut Skip<I>, n: usize, skipped: Ghost<Seq<<I::Item as Model>::Ty>>, self: thrust_models::FnParam<&mut Skip<I>>|
                    skipped.len() + n == (*self.at_entry()).1
                        && I::produces((*self.at_entry()).0, skipped, (*s).0)
                        && !s == !self.at_entry()
                        && (*s).1 == 0
                        && I::invariant((*s).0)
            );
            let r = s.iter.next();
            if n == 0 {
                return r;
            }
            if let Some(x) = r {
                skipped = thrust_macros::ghost!(|skipped: Ghost<Seq<<I::Item as Model>::Ty>>, x: I::Item| -> Seq<<I::Item as Model>::Ty> { skipped.concat(Seq::singleton(x)) });
                n -= 1
            } else {
                return r;
            }
        }
    }

    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        I::invariant(self.0) && self.1 >= 0
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        (!self).1 == 0
            && exists(|s: Seq<<Self::Item as Model>::Ty>| exists(|j: <I as Model>::Ty|
                s.len() <= (*self).1
                    && I::produces((*self).0, s, j)
                    && I::completed(Mut::new(j, (!self).0))))
    }

    // Creusot's statement: the inner iterator produces the `self.n` skipped items `s`, then
    // `visited`, as one concatenated sequence.
    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, o: Self) -> bool {
        (visited.len() == 0 && self == o)
            || (o.1 == 0
                && visited.len() > 0
                && exists(|s: Seq<<Self::Item as Model>::Ty>|
                    s.len() == self.1 + 1
                        && I::produces(self.0, s.concat(visited), o.0)))
    }
}

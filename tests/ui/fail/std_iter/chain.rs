//@ignore-on-host: draft: fptprove develop 3f9ee2482 gets no answer for `Chain`'s `produces_trans` (record 2026-10-25-rq4-std-iter-specs)
//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60

// A specification of std's `Chain` and `Iterator::chain`, kept out of std.rs until its laws are
// proved: with it, std.rs's law check (iterators/std_iterator_spec_laws.rs) gets no answer.
// The second iterator's item is not skipped.

// The two iterators it chains and whether the first is still there: std's `Chain` drops the
// first at its end and keeps the second (core/src/iter/adapters/chain.rs, `next`), and
// `chain` makes it with both.
impl<A, B> thrust_models::Model for core::iter::Chain<A, B>
where
    A: thrust_models::Model,
    B: thrust_models::Model,
{
    type Ty = (<A as thrust_models::Model>::Ty, <B as thrust_models::Model>::Ty, bool);
}

// std's `Chain` yields the items of its first iterator, drops it at its end, then yields those of
// the second (core/src/iter/adapters/chain.rs, `next`). Creusot specifies no `Chain`; the form is
// that of `Zip` above: each part's `produces`, joined where the first ends.
#[thrust_macros::context]
impl<A, B> IteratorSpec for core::iter::Chain<A, B>
where
    A: IteratorSpec<Item = <B as std::iter::Iterator>::Item>,
    B: IteratorSpec,
    A::Item: thrust_models::Model,
{
    #[thrust_macros::predicate]
    fn inv(self) -> bool {
        (!self.2 || A::inv(self.0)) && B::inv(self.1)
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Vec<A::Item>, o: Self) -> bool {
        // Still in the first iterator.
        (self.2 && o.2 && A::produces(self.0, visited, o.0) && o.1 == self.1)
        // Past it: what was left of it, completed, then a part of the second.
            || (self.2 && !o.2
                && thrust_models::exists(|va: thrust_models::model::Seq<<A::Item as thrust_models::Model>::Ty>,
                                          vb: thrust_models::model::Seq<<A::Item as thrust_models::Model>::Ty>,
                                          a2: <A as thrust_models::Model>::Ty,
                                          a3: <A as thrust_models::Model>::Ty|
                    visited == va.concat(vb)
                        && A::produces(self.0, va, a2)
                        && A::completed(thrust_models::model::Mut::new(a2, a3))
                        && B::produces(self.1, vb, o.1)))
        // In the second.
            || (!self.2 && !o.2 && B::produces(self.1, visited, o.1))
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        !(!self).2
            && (!(*self).2
                || thrust_models::exists(|a2: <A as thrust_models::Model>::Ty|
                    A::completed(thrust_models::model::Mut::new((*self).0, a2))))
            && B::completed(thrust_models::model::Mut::new((*self).1, (!self).1))
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

// `Iterator::chain`: both parts kept, the second converted by `into_iter`.
#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result.0 == a && result.2 && U::into_iter_is(b, result.1))]
fn _extern_spec_iterator_chain<A, U>(a: A, b: U) -> core::iter::Chain<A, U::IntoIter>
    where A: IteratorSpec<Item = <U as std::iter::IntoIterator>::Item>,
          U: IntoIteratorSpec,
          U::IntoIter: IteratorSpec,
          A::Item: thrust_models::Model
{
    <A as std::iter::Iterator>::chain(a, b)
}

fn main() {
    let a: Option<u32> = None;
    let b: Option<u32> = Some(5);
    let mut it = a.into_iter().chain(b);
    assert!(it.next() == None);
}

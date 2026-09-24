//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60 COAR_IMAGE=coar:latest
use thrust_models::forall;

#[thrust_macros::context]
trait Iterator {
    type Item;

    #[thrust_macros::requires(Self::invariant(*self))]
    #[thrust_macros::ensures(Self::invariant(!self))]
    #[thrust_macros::ensures(result == None ==> Self::completed(self))]
    #[thrust_macros::ensures(forall(|i| result == Some(i) ==> Self::step(*self, i, !self)))]
    #[thrust_macros::ensures(forall(|i| result == Some(i) ==> Self::produces(*self, i)))]
    #[thrust_macros::ensures(forall(|i| Self::produces(!self, i) ==> Self::produces(*self, i)))]
    fn next(&mut self) -> Option<Self::Item>;

    #[thrust_macros::predicate]
    fn invariant(self) -> bool;
    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool;
    #[thrust_macros::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool;
    /// `item` is among what `self` may still produce.
    #[thrust_macros::predicate]
    fn produces(self, item: Self::Item) -> bool;
}

struct Map<I, F> {
    iter: I,
    func: F,
}

impl<I, F> thrust_models::Model for Map<I, F> {
    type Ty = Map<I, F>;
}

#[thrust_macros::context]
impl<I: Iterator<Item = i64> + thrust_models::Model, F: Fn(i64) -> i64> Iterator for Map<I, F>
where
    <I as thrust_models::Model>::Ty: PartialEq,
{
    type Item = i64;

    fn next(&mut self) -> Option<Self::Item> {
        match self.iter.next() {
            Some(v) => Some((self.func)(v)),
            None => None,
        }
    }

    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        // self.iter.invariant() &&
        // forall(|e: i64| self.iter.produces(e) ==> pre!(self.func(e)))
        //
        // The guard is unary: the mapper's precondition is demanded only of items
        // the inner iterator may still produce. No iterator state is bound, which
        // is what keeps the call-site discharge tractable.
        "(and
            (q_invariant_591fb6d09db8ba7642c3faf1441888f5<a0> (tuple_proj<a0-a1>.0 self_))
            (forall ((ze Int))
                (=>
                    (q_produces_591fb6d09db8ba76ef361a07a03d5396<a0> (tuple_proj<a0-a1>.0 self_) ze)
                    (q_pre_next_591fb6d09db8ba76fdf5e092b27c5f90<a1> (tuple_proj<a0-a1>.1 self_) ze)
                )
            )
        )";
        true
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        // self.iter.completed() && *self.func == !self.func
        "(and
            (q_completed_591fb6d09db8ba7635474649aefe1353<a0>
                (mut<a0>
                    (tuple_proj<a0-a1>.0 (mut_current<Tuple<a0-a1>> self_))
                    (tuple_proj<a0-a1>.0 (mut_final<Tuple<a0-a1>> self_))
                )
            )
            (=
                (tuple_proj<a0-a1>.1 (mut_current<Tuple<a0-a1>> self_))
                (tuple_proj<a0-a1>.1 (mut_final<Tuple<a0-a1>> self_))
            )
        )";
        true
    }

    #[thrust_macros::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool {
        // exists(|i: i64| self.iter.step(i, dist.iter)
        //     && pre!(self.func(i)) && post!(self.func(i), item))
        // && self.func == dist.func
        "(exists ((zi Int))
            (and
                (q_step_591fb6d09db8ba76e4cecfffeed95b1e<a0> (tuple_proj<a0-a1>.0 self_) zi (tuple_proj<a0-a1>.0 dist))
                (q_pre_next_591fb6d09db8ba76fdf5e092b27c5f90<a1> (tuple_proj<a0-a1>.1 self_) zi)
                (q_post_next_591fb6d09db8ba76fdf5e092b27c5f90<a1> (tuple_proj<a0-a1>.1 self_) zi item)
                (= (tuple_proj<a0-a1>.1 self_) (tuple_proj<a0-a1>.1 dist))
            )
        )";
        true
    }

    #[thrust_macros::predicate]
    fn produces(self, item: Self::Item) -> bool {
        // exists(|j: i64| self.iter.produces(j)
        //     && pre!(self.func(j)) && post!(self.func(j), item))
        "(exists ((zj Int))
            (and
                (q_produces_591fb6d09db8ba76ef361a07a03d5396<a0> (tuple_proj<a0-a1>.0 self_) zj)
                (q_pre_next_591fb6d09db8ba76fdf5e092b27c5f90<a1> (tuple_proj<a0-a1>.1 self_) zj)
                (q_post_next_591fb6d09db8ba76fdf5e092b27c5f90<a1> (tuple_proj<a0-a1>.1 self_) zj item)
            )
        )";
        true
    }
}

fn main() {}

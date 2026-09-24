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
    // A guard over `step` (one call ahead) is not preserved by `next`; `produces` is
    // monotone under `next`, which makes Map's invariant inductive.
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
    // The inner iterator
    iter: I,
    // The mapper
    func: F,
}

impl<I, F> thrust_models::Model for Map<I, F> {
    type Ty = Map<I, F>;
}

#[thrust_macros::context]
impl<I: Iterator + thrust_models::Model, B: thrust_models::Model, F: Fn(I::Item) -> B> Iterator for Map<I, F>
where <I as thrust_models::Model>::Ty: PartialEq
{
    type Item = B;
    
    fn next(&mut self) -> Option<Self::Item> {
        match self.iter.next() {
            Some(v) => {
                Some((self.func)(v))
            }
            None => None,
        }
    }

    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        // self.iter.invariant() &&
        // forall(|i: I::Item| self.iter.produces(i) ==> pre!(self.func(i)))
        "(and
            (q_invariant_ae8bdb3b1e3ae00bdd84dd265c9192eb<a0> (tuple_proj<a0-a1>.0 self_))
            (forall ((i a3))
                (=>
                    (q_produces_ae8bdb3b1e3ae00b78c5ded836701e16<a0>
                        (tuple_proj<a0-a1>.0 self_)
                        i
                    )
                    (q_pre_F_ae8bdb3b1e3ae00b829c53733665345c<a1>
                        (tuple_proj<a0-a1>.1 self_)
                        i
                    )
                )
            )
        )";
        true
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        // self.iter.completed() && *self.func == !self.func
        "(and
            (q_completed_ae8bdb3b1e3ae00b46c4745e3c9b07d6<a0>
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
        // exists(|i: I::Item| self.iter.step(i, dist.iter)
        //     && pre!(self.func(i)) && post!(self.func(i), item))
        // && self.func == dist.func
        "(exists ((i a3))
            (and
                (q_step_ae8bdb3b1e3ae00b8dd88201ff820b9d<a0>
                    (tuple_proj<a0-a1>.0 self_)
                    i
                    (tuple_proj<a0-a1>.0 dist)
                )
                (q_pre_F_ae8bdb3b1e3ae00b829c53733665345c<a1>
                    (tuple_proj<a0-a1>.1 self_)
                    i
                )
                (q_post_F_ae8bdb3b1e3ae00b829c53733665345c<a1>
                    (tuple_proj<a0-a1>.1 self_)
                    i
                    item
                )
                (= (tuple_proj<a0-a1>.1 self_) (tuple_proj<a0-a1>.1 dist))
            )
        )";
        true
    }

    #[thrust_macros::predicate]
    fn produces(self, item: Self::Item) -> bool {
        // exists(|j: I::Item| self.iter.produces(j)
        //     && pre!(self.func(j)) && post!(self.func(j), item))
        "(exists ((j a3))
            (and
                (q_produces_ae8bdb3b1e3ae00b78c5ded836701e16<a0>
                    (tuple_proj<a0-a1>.0 self_)
                    j
                )
                (q_pre_F_ae8bdb3b1e3ae00b829c53733665345c<a1>
                    (tuple_proj<a0-a1>.1 self_)
                    j
                )
                (q_post_F_ae8bdb3b1e3ae00b829c53733665345c<a1>
                    (tuple_proj<a0-a1>.1 self_)
                    j
                    item
                )
            )
        )";
        true
    }
}

fn main() {}

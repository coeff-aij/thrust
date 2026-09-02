//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest
use thrust_models::forall;

#[thrust_macros::context]
trait Iterator {
    type Item;

    #[thrust_macros::requires(Self::invariant(*self))]
    #[thrust_macros::ensures(result == None ==> Self::completed(self))]
    #[thrust_macros::ensures(Self::completed(self) ==> result == None)]
    #[thrust_macros::ensures(forall(|i| result == Some(i) ==> Self::step(*self, i, !self)))]
    #[thrust_macros::ensures(forall(|i| Self::step(*self, i, !self) ==> result == Some(i)))]
    fn next(&mut self) -> Option<Self::Item>;

    #[thrust_macros::predicate]
    fn invariant(self) -> bool;
    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool;
    #[thrust_macros::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool;
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
        // forall(|i: Self::Item| forall(|dist: I|
        //     self.iter.step(i, dist) ==>
        //     exists(|f: F| call_pre!(Mut::new(self.func, f)(i)))
        // )))
        "(and
            (q_invariant_7301c9248155c50d8ab3300ff35fd085<a0> (tuple_proj<a0-a1>.0 self_))
            (or
                (exists ((dist a0))
                    (q_completed_7301c9248155c50da4cf4c72232b5d2b<a0>
                        (mut<a0>
                            (tuple_proj<a0-a1>.0 self_)
                            dist
                        )
                    )
                )
                (and
                    (exists ((i a3) (dist a0))
                        (q_step_7301c9248155c50d139c4cfe897a4790<a0>
                            (tuple_proj<a0-a1>.0 self_)
                            i
                            dist
                        )
                    )
                    (forall ((i a3) (dist a0))
                        (=>
                            (q_step_7301c9248155c50d139c4cfe897a4790<a0>
                                (tuple_proj<a0-a1>.0 self_)
                                i
                                dist
                            )
                            (exists ((f a1))
                                (q_pre_next_7301c9248155c50de744744ab31cecba<a1>
                                    (tuple_proj<a0-a1>.1 self_)
                                    i
                                )
                            )
                        )
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
            (q_completed_7301c9248155c50da4cf4c72232b5d2b<a0>
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
        // exists(|i: Self::Item| self.iter.step(i, dist.iter)) &&
        // pre!(self.func(i)) && post!(self.func(i), item)
        "(exists ((i a3))
            (and
                (q_step_7301c9248155c50d139c4cfe897a4790<a0>
                    (tuple_proj<a0-a1>.0 self_)
                    i
                    (tuple_proj<a0-a1>.0 dist)
                )
                (q_pre_next_7301c9248155c50de744744ab31cecba<a1>
                    (tuple_proj<a0-a1>.1 self_)
                    i
                )
                (q_post_next_7301c9248155c50de744744ab31cecba<a1>
                    (tuple_proj<a0-a1>.1 self_)
                    i item
                )
                (=
                    (tuple_proj<a0-a1>.1 self_)
                    (tuple_proj<a0-a1>.1 dist)
                )
            )
        )";
        true
    }
}

fn main() {}

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
impl<I: Iterator + thrust_models::Model, B: thrust_models::Model, F: FnMut(I::Item) -> B> Iterator for Map<I, F>
where 
    <B as thrust_models::Model>::Ty: PartialEq,
    I: Iterator + thrust_models::Model,
    <I as Iterator>::Item: thrust_models::Model,
    <I as thrust_models::Model>::Ty: PartialEq,
{
    type Item = <I as Iterator>::Item;
    
    fn next(&mut self) -> Option<Self::Item> {
        match self.iter.next() {
            Some(v) => {
                Some(v)
            }
            None => None,
        }
    }

    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        // self.iter.invariant() && (
        //     exists(|dist: I| I::completed(Mut::new(self.iter, dist))) ||
        //     (exists(|i: Self::Item| exists(|dist: I|
        //         self.iter.step(i, dist)
        //     )) && 
        //     forall(|i: Self::Item| forall(|dist: I|
        //         self.iter.step(i, dist) ==>
        //         exists(|f: F| call_pre!(Mut::new(self.func, f)(i)))
        //     )))
        // )
        "(and
            (q_invariant_99f65cdf4976362522ac567242ed1838<a0> (tuple_proj<a0-a1>.0 self_))
            (or
                (exists ((dist a0))
                    (q_completed_99f65cdf497636256ec9953086464b7d<a0>
                        (mut<a0>
                            (tuple_proj<a0-a1>.0 self_)
                            dist
                        )
                    )
                )
                (and
                    (exists ((i a2) (dist a0))
                        (q_step_99f65cdf4976362561bb73a005eacf63<a0>
                            (tuple_proj<a0-a1>.0 self_)
                            i
                            dist
                        )
                    )
                    (forall ((i a2) (dist a0))
                        (=>
                            (q_step_99f65cdf4976362561bb73a005eacf63<a0>
                                (tuple_proj<a0-a1>.0 self_)
                                i
                                dist
                            )
                            (exists ((f Mut<a1>))
                                (q_pre_next_99f65cdf49763625952b80f71d0217f8<a1>
                                    f
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
            (q_completed_99f65cdf497636256ec9953086464b7d<a0>
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
        // self.iter.step(item, dist.iter) && self.func == dist.func
        "(and
            (q_step_99f65cdf4976362561bb73a005eacf63<a0>
                (tuple_proj<a0-a1>.0 self_)
                item
                (tuple_proj<a0-a1>.0 dist)
            )
            (=
                (tuple_proj<a0-a1>.1 self_)
                (tuple_proj<a0-a1>.1 self_)
            )
        )";
        true
    }
}

fn main() {}

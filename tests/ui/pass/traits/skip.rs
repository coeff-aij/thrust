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
    fn next(&mut self) -> Option<Self::Item>;

    #[thrust_macros::predicate]
    fn invariant(self) -> bool;
    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool;
    #[thrust_macros::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool;
}

pub struct Skip<I> {
    iter: I,
    n: usize,
}

impl<I> thrust_models::Model for Skip<I> {
    type Ty = Skip<I>;
}

#[thrust_macros::context]
impl<I> Iterator for Skip<I>
where
    I: Iterator + thrust_models::Model,
    <I as thrust_models::Model>::Ty: PartialEq,
    <I as Iterator>::Item: thrust_models::Model,
{
    type Item = I::Item;

    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        // self.iter.invariant() && self.n >= 0
        "(and
            (q_invariant_5131ffd98a13a5371cc2c08cc3297186<a0>
                (tuple_proj<a0-Int>.0 self_))
            (>= (tuple_proj<a0-Int>.1 self_) 0))";
        true
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        // self.iter.completed() && self.n == 0
        "(and
            (q_completed_5131ffd98a13a537b39009f840ff9d54<a0>
                (mut<a0>
                    (tuple_proj<a0-Int>.0 (mut_current<Tuple<a0-Int>> self_))
                    (tuple_proj<a0-Int>.0 (mut_final<Tuple<a0-Int>> self_))))
            (= (tuple_proj<a0-Int>.1 (mut_current<Tuple<a0-Int>> self_)) 0))";
        true
    }

    #[thrust_macros::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool {
        // if n == 0 {
        //      self.step(item, dist)
        // } else {
        //      exists(|iters: Array<Int, Iterator>|
        //          exists(|i0: Item| self.iter.step(i0, iters[1])
        //          && forall(|k: Int| if 1 <= k && k < n {
        //              exists(|i: Item| iters[k].step(i, iters[k + 1]))})
        //          && iters[n].step(item, dist.iter))))
        // }
        "(ite
            (= (tuple_proj<a0-Int>.1 self_) 0)
            (q_step_5131ffd98a13a53768727aaca4694b97<a0>
                (tuple_proj<a0-Int>.0 self_)
                item
                (tuple_proj<a0-Int>.0 dist))
            (exists ((iters (Array Int a0)))
                (and
                    (exists ((i0 a1))
                        (q_step_5131ffd98a13a53768727aaca4694b97<a0>
                            (tuple_proj<a0-Int>.0 self_)
                            i0
                            (select iters 1)))
                    (forall ((k Int))
                        (=>
                            (and
                                (<= 1 k)
                                (< k (tuple_proj<a0-Int>.1 self_)))
                            (exists ((i a1))
                                (q_step_5131ffd98a13a53768727aaca4694b97<a0>
                                    (select iters k)
                                    i
                                    (select iters (+ k 1))))))
                    (q_step_5131ffd98a13a53768727aaca4694b97<a0>
                        (select iters (tuple_proj<a0-Int>.1 self_))
                        item
                        (tuple_proj<a0-Int>.0 dist)))))";
        true
    }

    fn next(&mut self) -> Option<I::Item> {
        while self.n > 0 {
            self.iter.next();
            self.n -= 1;
        }

        self.iter.next()
    }
}

fn main() {}

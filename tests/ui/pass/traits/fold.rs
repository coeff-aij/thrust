//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60 COAR_IMAGE=coar:latest

use thrust_models::{exists, forall, Model, model::{Array, Int, Mut, Closure}};

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

    
    #[thrust_macros::requires(
        exists(|it: Array<Int, <Self as Model>::Ty>|
        exists(|fn_: Array<Int, Closure<F>>|
        exists(|acc: Array<Int, <B as Model>::Ty>|
        exists(|l: Int|
            it[0] == self &&
            fn_[0] == f &&
            acc[0] == init &&
            Self::completed(Mut::new(it[l - 1], it[l])) &&
            exists(|item|
            !Self::completed(Mut::new(it[l - 2], it[l - 1])) &&
            Self::step(it[l - 2], item, it[l - 1]) &&
            thrust_macros::pre!(Mut::new(fn_[l - 2], fn_[l - 1])(acc[l - 2], item)) 
            ) &&
            forall(|i: Int|
                0 <= i && i < l - 2 ==>
                exists(|item|
                    !Self::completed(Mut::new(it[i], it[i + 1])) &&
                    Self::step(it[i], item, it[i + 1]) &&
                    thrust_macros::pre!(Mut::new(fn_[i], fn_[i + 1])(acc[i], item)) &&
                    thrust_macros::post!(
                        Mut::new(fn_[i], fn_[i + 1])(acc[i], item),
                        acc[i + 1]
                    )
                )
            )
        ))))
    )]
    #[thrust_macros::ensures(
        exists(|it: Array<Int, <Self as Model>::Ty>|
        exists(|fn_: Array<Int, Closure<F>>|
        exists(|acc: Array<Int, <B as Model>::Ty>|
        exists(|l: Int|
            it[0] == self &&
            fn_[0] == f &&
            acc[0] == init &&
            Self::completed(Mut::new(it[l - 1], it[l])) &&
            result == acc[l - 1] &&
            forall(|i: Int|
                0 <= i && i < l - 1 ==>
                exists(|item|
                    !Self::completed(Mut::new(it[i], it[i + 1])) &&
                    Self::step(it[i], item, it[i + 1]) &&
                    thrust_macros::pre!(Mut::new(fn_[i], fn_[i + 1])(acc[i], item)) &&
                    thrust_macros::post!(
                        Mut::new(fn_[i], fn_[i + 1])(acc[i], item),
                        acc[i + 1]
                    )
                )
            )
        ))))
    )]
    fn fold<B, F>(mut self, init: B, mut f: F) -> B
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> B,
    {
        let mut accum = init;
        while let Some(x) = self.next() {
            thrust_macros::invariant!(
                |accum: B, init: thrust_models::FnParam<B>, f: F, self: Self|
                exists(|it: Array<Int, <Self as Model>::Ty>|
                exists(|fn_: Array<Int, Closure<F>>|
                exists(|acc: Array<Int, <B as Model>::Ty>|
                exists(|l: Int|
                    it[0] == self &&
                    fn_[0] == f &&
                    acc[0] == init.at_entry() &&
                    accum == acc[l - 1] &&
                    forall(|i: Int|
                        0 <= i && i < l - 1 ==>
                        exists(|item: <Self::Item as Model>::Ty|
                            !Self::completed(Mut::new(it[i], it[i + 1])) &&
                            Self::step(it[i], item, it[i + 1]) &&
                            thrust_macros::pre!(Mut::new(fn_[i], fn_[i + 1])(acc[i], item)) &&
                            thrust_macros::post!(
                                Mut::new(fn_[i], fn_[i + 1])(acc[i], item),
                                acc[i + 1]
                            )
                        )
                    )
                ))))
            );
            accum = f(accum, x);
        }
        accum
    }
}

fn main() {}

//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60 COAR_IMAGE=coar:latest

use thrust_models::{exists, forall, FnParam, Model, model::{Array, Int, Mut, Closure}};

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

    #[thrust_macros::requires(
        forall(|l: Int|
        forall(|it: Array<Int, <Self as Model>::Ty>|
        forall(|items: Array<Int, <Self::Item as Model>::Ty>|
        exists(|f_final: Closure<F>|
            l >= 1 &&
            it[0] == self &&
            forall(|i: Int|
                0 <= i && i < l - 1
                ==> Self::step(it[i], items[i], it[i + 1])
            ) ==> (
                (
                    exists(|fn_: Array<Int, Closure<F>>|
                    exists(|acc: Array<Int, <B as Model>::Ty>|
                        fn_[0] == f &&
                        acc[0] == init &&
                        forall(|i: Int|
                            0 <= i && i < l - 1 ==> (
                                thrust_macros::pre!(Mut::new(fn_[i], f_final)(acc[i], items[i])) &&
                                thrust_macros::post!(
                                    Mut::new(fn_[i], f_final)(acc[i], items[i]),
                                    acc[i + 1]
                                )
                            )
                        )
                    ))
                ) &&
                (
                    forall(|k: Int|
                        k < l ==>
                        forall(|fn_: Array<Int, Closure<F>>|
                        forall(|acc: Array<Int, <B as Model>::Ty>|
                            (
                                fn_[0] == f &&
                                acc[0] == init &&
                                forall(|i: Int|
                                    0 <= i && i < k - 1 ==> (
                                        thrust_macros::pre!(Mut::new(fn_[i], f_final)(acc[i], items[i])) &&
                                        thrust_macros::post!(
                                            Mut::new(fn_[i], f_final)(acc[i], items[i]),
                                            acc[i + 1]
                                        )
                                    )
                                )
                            ) ==> (
                                exists(|next_f: Closure<F>|
                                    thrust_macros::pre!(Mut::new(fn_[k - 1], f_final)(acc[k - 1], items[k - 1]))
                                )
                            )
                        ))
                    )
                )
            )
        ))))
    )]
    #[thrust_macros::ensures(
        exists(|l: Int|
        exists(|it: Array<Int, <Self as Model>::Ty>|
        exists(|items: Array<Int, <Self::Item as Model>::Ty>|
        exists(|f_final: Closure<F>|
        exists(|fn_: Array<Int, Closure<F>>|
        exists(|acc: Array<Int, <B as Model>::Ty>|
            l >= 1 &&
            it[0] == self &&
            fn_[0] == f &&
            acc[0] == init &&
            Self::completed(Mut::new(it[l - 1], it[l])) &&
            result == acc[l - 1] &&
            forall(|i: Int|
                0 <= i && i < l - 1 ==> (
                    Self::step(it[i], items[i], it[i + 1]) &&
                    thrust_macros::pre!(Mut::new(fn_[i], f_final)(acc[i], items[i])) &&
                    thrust_macros::post!(
                        Mut::new(fn_[i], f_final)(acc[i], items[i]),
                        acc[i + 1]
                    )
                )
            )
        ))))))
    )]
    fn fold<B, F>(mut self, init: B, mut f: F) -> B
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> B,
    {
        let mut accum = init;
        let mut self_ = self;
        let mut f_ = f;
        while let Some(x) = self_.next() {
            thrust_macros::invariant!(
                |self: FnParam<Self>, init: FnParam<B>, f: FnParam<F>, accum: B, self_: Self, f_: F|
                exists(|l: Int|
                exists(|it: Array<Int, <Self as Model>::Ty>|
                exists(|items: Array<Int, <Self::Item as Model>::Ty>|
                exists(|f_final: Closure<F>|
                exists(|fn_: Array<Int, Closure<F>>|
                exists(|acc: Array<Int, <B as Model>::Ty>|
                    l >= 0 &&
                    it[0] == self.at_entry() &&
                    fn_[0] == f.at_entry() &&
                    acc[0] == init.at_entry() &&
                    it[l - 1] == self_ &&
                    fn_[l - 1] == f_ &&
                    acc[l - 1] == accum &&
                    forall(|i: Int|
                        0 <= i && i < l - 1 ==> (
                            Self::step(it[i], items[i], it[i + 1]) &&
                            thrust_macros::pre!(Mut::new(fn_[i], f_final)(acc[i], items[i])) &&
                            thrust_macros::post!(
                                Mut::new(fn_[i], f_final)(acc[i], items[i]),
                                acc[i + 1]
                            )
                        )
                    )
                ))))))
            );
            accum = f_(accum, x);
        }
        accum
    }
}

fn main() {}

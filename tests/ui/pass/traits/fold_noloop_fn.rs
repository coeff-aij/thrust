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
        Self::invariant(self) &&
        forall(|it: <Self as Model>::Ty|
        forall(|item|
            Self::step(self, item, it)
            ==> thrust_macros::pre!(f(init, item))
        ))
    )]
    #[thrust_macros::ensures(
        forall(|it: <Self as Model>::Ty|
        forall(|item|
            Self::step(self, item, it) ==> (
                thrust_macros::pre!(f(init, item)) &&
                thrust_macros::post!(f(init, item), result)
            )
        ))
    )]
    #[thrust_macros::ensures(
        exists(|it: <Self as Model>::Ty|
         Self::completed(Mut::new(self, it)) ==> result == init
        )
    )]
    fn fold<B, F>(mut self, init: B, f: F) -> B
    where
        Self: Sized,
        F: Fn(B, Self::Item) -> B,
    {
        let mut accum = init;
        if let Some(x) = self.next() {
            accum = f(accum, x);
        }
        accum
    }
}

fn main() {}

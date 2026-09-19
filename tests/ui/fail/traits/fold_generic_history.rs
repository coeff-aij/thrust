//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60 COAR_IMAGE=coar:latest

use thrust_models::forall;
use thrust_models::model::{Int, Seq};
use thrust_models::{FnParam, Ghost, Model};

/// The item and accumulator histories a `fold` walks over, as ghost state the body
/// extends rather than as values a solver has to invent.
struct History<T: Model, B: Model> {
    items: Ghost<Seq<<T as Model>::Ty>>,
    accs: Ghost<Seq<<B as Model>::Ty>>,
}

impl<T: Model, B: Model> Model for History<T, B> {
    type Ty = (Seq<<T as Model>::Ty>, Seq<<B as Model>::Ty>);
}

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

    #[thrust_macros::requires(
        Self::invariant(self)
            && (*h).0.len() == 0
            && (*h).1.len() == 1
            && (*h).1[0] == init
            && forall(|a: <B as Model>::Ty| forall(|x: <Self::Item as Model>::Ty|
                Self::produces(self, x) ==> thrust_macros::pre!(f(a, x))
            ))
    )]
    #[thrust_macros::ensures(
        result == (!h).1[(!h).0.len()]
            && (!h).1.len() == (!h).0.len() + 1
            && forall(|k: Int|
                0 <= k && k < (!h).0.len()
                    ==> thrust_macros::post!(f((!h).1[k], (!h).0[k]), (!h).1[k + 1])
            )
    )]
    fn fold<B, F>(self, h: &mut History<Self::Item, B>, init: B, f: F) -> B
    where
        Self: Sized,
        Self::Item: Model,
        <Self::Item as Model>::Ty: PartialEq,
        B: Model,
        <B as Model>::Ty: PartialEq,
        F: Fn(B, Self::Item) -> B,
    {
        let hh = h;
        let mut self_ = self;
        let mut acc = init;
        let mut cnt = 0;
        while let Some(x) = self_.next() {
            thrust_macros::invariant!(
                |self_: Self,
                 hh: &mut History<Self::Item, B>,
                 h: FnParam<&mut History<Self::Item, B>>,
                 f: F,
                 acc: B,
                 cnt: i64|
                Self::invariant(self_)
                    && !hh == !h.at_entry()
                    && 0 <= cnt
                    && (*hh).0.len() == cnt
                    && (*hh).1.len() == (*hh).0.len() + 1
                    && acc == (*hh).1[(*hh).0.len()]
                    && forall(|a: <B as Model>::Ty| forall(|x: <Self::Item as Model>::Ty|
                        Self::produces(self_, x) ==> thrust_macros::pre!(f(a, x))
                    ))
                    && forall(|k: Int|
                        0 <= k && k < (*hh).0.len()
                            ==> thrust_macros::post!(f((*hh).1[k], (*hh).0[k]), (*hh).1[k + 1])
                    )
            );
            hh.items = thrust_macros::ghost!(
                |hh: &mut History<Self::Item, B>, x: Self::Item|
                    -> Seq<<Self::Item as Model>::Ty> { (*hh).0.push(x) }
            );
            hh.accs = thrust_macros::ghost!(
                |hh: &mut History<Self::Item, B>, acc: B| -> Seq<<B as Model>::Ty> {
                    (*hh).1.push(acc)
                }
            );
            acc = f(acc, x);
            cnt += 1;
        }
        acc
    }
}

fn main() {}

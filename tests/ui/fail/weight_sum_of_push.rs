//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -A unused-variables -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

use thrust_models::model::{Int, Seq, UInt};
use thrust_models::{exists, forall};
use thrust_models::Model;

// The weight of a list of `F`s, each read through `Deref::deref`, whose `post!` at a type
// parameter is a relation. The value `deref` returns is named by a total logic function of the
// trait (`weight_of`), which the graph of `deref` ties to the code (`deref_graph`), so the weight
// of a list is a recursive logic function (`sum_of`) with no existential to give a witness for.

#[thrust_macros::context]
trait Weighted: core::ops::Deref<Target = u64> + Copy + Model
where
    <Self as Model>::Ty: Model<Ty = <Self as Model>::Ty>,
{
    #[thrust_macros::logic]
    fn weight_of(x: <Self as Model>::Ty) -> Int;
}

#[thrust_macros::context]
#[thrust_macros::predicate]
fn deref_graph<F: Weighted>() -> bool
where <F as Model>::Ty: Model<Ty = <F as Model>::Ty>,
{
    forall(|x: <F as Model>::Ty, d: &u64|
        !thrust_macros::post!(<F as core::ops::Deref>::deref(&x), d) || *d == F::weight_of(x))
}

#[thrust_macros::context]
#[thrust_macros::logic]
#[thrust_macros::variant(k)]
fn sum_of<F: Weighted>(s: Seq<<F as Model>::Ty>, k: UInt) -> Int
where <F as Model>::Ty: Model<Ty = <F as Model>::Ty>,
{
    if k <= 0 { 0 } else { sum_of::<F>(s, k - 1) + F::weight_of(s[k - 1]) }
}

#[thrust_macros::context]
#[thrust_macros::requires(deref_graph::<F>())]
#[thrust_macros::requires(w == sum_of::<F>(*s, (*s).len()))]
#[thrust_macros::requires(exists(|d: &u64| thrust_macros::post!(<F as core::ops::Deref>::deref(x), d) && *d == wx))]
#[thrust_macros::ensures(w + wx + 1 == sum_of::<F>((*s).push(*x), (*s).len() + 1))]
fn weight_push<F: Weighted>(s: &Vec<F>, x: &F, wx: i64, w: i64)
where <F as Model>::Ty: Model<Ty = <F as Model>::Ty>,
{
}

fn main() {}

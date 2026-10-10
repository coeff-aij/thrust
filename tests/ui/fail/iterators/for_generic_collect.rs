//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The pass twin keeping only the first item.

use thrust_models::model::Seq;
use thrust_models::{Ghost, Model};

#[thrust_macros::context]
#[thrust_macros::requires(I::inv(it))]
#[thrust_macros::ensures(thrust_models::exists(|last: I::Ty| thrust_models::exists(|fin: I::Ty|
    I::produces(it, result, last) && I::completed(thrust_models::model::Mut::new(last, fin)))))]
fn collect<I: IteratorSpec>(it: I) -> Vec<I::Item>
where
    I::Item: Model,
    I::Ty: PartialEq,
    <I::Item as Model>::Ty: PartialEq,
{
    let mut out = Vec::new();
    for x in it {
        thrust_macros::invariant!(|iter: I, iter_old: Ghost<I>, produced: Ghost<Seq<<I::Item as Model>::Ty>>, out: Vec<I::Item>, it: thrust_models::FnParam<I>|
            iter_old == it.at_entry() && out == produced);
        if out.len() == 0 {
            out.push(x);
        }
    }
    out
}

fn main() {}

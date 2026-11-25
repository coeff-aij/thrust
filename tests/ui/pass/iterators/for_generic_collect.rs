//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// Creusot's collecting `for` loop over a type parameter bounded by `IteratorSpec`: the vector is
// `produced`, so the structural invariant and the laws give the postcondition.
use thrust_models::{exists, FnParam, model::Mut};
use thrust_models::model::Seq;
use thrust_models::{Ghost, Model};

#[thrust_macros::context]
#[thrust_macros::requires(I::inv(it))]
#[thrust_macros::ensures(exists(|last: I::Ty| exists(|fin: I::Ty|
    I::produces(it, result, last) && I::completed(Mut::new(last, fin)))))]
fn collect<I: IteratorSpec>(it: I) -> Vec<I::Item>
where
    I::Item: Model,
{
    let mut out = Vec::new();
    for x in it {
        thrust_macros::invariant!(|iter: I, iter_old: Ghost<I>, produced: Ghost<Seq<<I::Item as Model>::Ty>>, out: Vec<I::Item>, it: FnParam<I>|
            iter_old == it.at_entry() && out == produced);
        out.push(x);
    }
    out
}

fn main() {}

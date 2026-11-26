//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A `while let Some(x) = it.next()` loop at a type parameter with an `IteratorSpec` bound. `next`
// gives one step at a time; `produces_refl` and `produces_trans` are what let the invariant hold
// the whole history, so the collected vector is exactly what the iterator produced until it was
// completed.
use thrust_models::{exists, FnParam, Model, model::Mut};
#[thrust_macros::context]
#[thrust_macros::ensures(exists(|last: I::Ty| exists(|fin: I::Ty|
    I::produces(iter, result, fin) && I::completed(Mut::new(last, fin)))))]
fn collect<I: IteratorSpec>(iter: I) -> Vec<I::Item>
where
    I::Item: Model,
{
    let mut it = iter;
    let mut out = Vec::new();
    while let Some(x) = it.next() {
        thrust_macros::invariant!(|it: I, out: Vec<I::Item>, iter: FnParam<I>|
            I::inv(it) && I::produces(iter.at_entry(), out, it));
        out.push(x);
    }
    out
}

fn main() {}

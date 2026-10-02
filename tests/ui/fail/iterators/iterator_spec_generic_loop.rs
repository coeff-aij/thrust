//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A `while let Some(x) = it.next()` loop at a type parameter with an `IteratorSpec` bound. `next`
// gives one step at a time; `produces_refl` and `produces_trans` are what let the invariant hold
// the whole history, so the collected vector is exactly what the iterator produced until it was
// completed.

#[thrust_macros::context]
#[thrust_macros::ensures(thrust_models::exists(|last: I::Ty| thrust_models::exists(|fin: I::Ty|
    I::produces(iter, result, fin) && I::completed(thrust_models::model::Mut::new(last, fin)))))]
fn collect<I: IteratorSpec>(iter: I) -> Vec<I::Item>
where
    I::Item: thrust_models::Model,
    I::Ty: PartialEq,
    <I::Item as thrust_models::Model>::Ty: PartialEq,
{
    let mut it = iter;
    let mut out = Vec::new();
    while let Some(x) = it.next() {
        thrust_macros::invariant!(|it: I, out: Vec<I::Item>, iter: thrust_models::FnParam<I>|
            I::produces(iter.at_entry(), out, it));
        out.push(x);
    }
    out
}

fn main() {}

//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:0360cb142

// `next` at a type parameter with an `IteratorSpec` bound: `None` means the iterator is completed.

#[thrust_macros::context]
#[thrust_macros::ensures(result == false ==> I::completed(it))]
fn exhausted<I: IteratorSpec>(it: &mut I) -> bool
where
    I::Item: thrust_models::Model,
    I::Ty: PartialEq,
    <I::Item as thrust_models::Model>::Ty: PartialEq,
{
    match it.next() {
        None => true,
        Some(_) => false,
    }
}

fn main() {}

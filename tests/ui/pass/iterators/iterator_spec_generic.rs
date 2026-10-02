//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `next` at a type parameter with an `IteratorSpec` bound: `None` means the iterator is completed.

#[thrust_macros::context]
#[thrust_macros::ensures(result == true ==> I::completed(it))]
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

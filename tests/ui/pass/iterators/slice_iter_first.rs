//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest

// `slice::Iter` is the `(base, cursor)` pair of the sequence it was made from and the position
// of the element the next `next` returns, so the element `next` hands back is named without a
// quantifier and without a loop.

#[thrust_macros::requires((*s).length > 0)]
#[thrust_macros::ensures(result == (*s).array[0])]
fn head<T>(s: &[T]) -> T
    where T: thrust_models::Model + Copy, T::Ty: PartialEq
{
    let mut it = s.iter();
    match it.next() {
        Some(x) => *x,
        None => s[0],
    }
}

fn main() {}

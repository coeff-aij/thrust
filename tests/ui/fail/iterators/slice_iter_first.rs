//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest

// The element `next` hands back is the one at the cursor, which starts at 0: claiming the
// element at 1 is false of every slice with a different pair of leading elements.

#[thrust_macros::requires((*s).len() > 0)]
#[thrust_macros::ensures(result == (*s)[1])]
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

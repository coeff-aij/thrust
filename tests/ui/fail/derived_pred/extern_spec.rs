//@compile-flags: -C debug-assertions=off -A unused-variables -A dead_code
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// Rejected, not Unsat. An extern specification of a foreign function assumes `produces` in a
// premise: no body of the crate proves it.

#[thrust_macros::context]
trait Iter {
    type Item;

    #[thrust_macros::predicate(derived)]
    fn produces(self, item: Self::Item) -> bool;

    #[thrust_macros::ensures(thrust_models::forall(|i| result == Some(i) ==> Self::produces(*self, i)))]
    fn next(&mut self) -> Option<Self::Item>;
}

#[thrust_macros::context]
impl Iter for u32 {
    type Item = u32;

    fn next(&mut self) -> Option<u32> {
        if *self < 5 {
            let item = *self;
            *self += 1;
            Some(item)
        } else {
            None
        }
    }
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(<u32 as Iter>::produces(x, n) ==> n < 5)]
fn _extern_spec_u32_rotate_left(x: u32, n: u32) -> u32 {
    u32::rotate_left(x, n)
}

fn main() {
    let _ = 0u32.rotate_left(7); //~ ERROR: the postcondition of this call
    assert!(false);
}

//@compile-flags: -C debug-assertions=off -A unused-variables -A dead_code
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// Rejected. A generic impl may not leave a derived predicate out: its rules would have to be
// instantiated with the impl.

#[thrust_macros::context]
trait Iter {
    type Item;

    #[thrust_macros::predicate(derived)]
    fn produces(self, item: Self::Item) -> bool;

    fn next(&mut self) -> Option<Self::Item>;
}

#[derive(PartialEq)]
struct Rep<T> {
    v: T,
}

impl<T: thrust_models::Model> thrust_models::Model for Rep<T> {
    type Ty = Rep<T::Ty>;
}

#[thrust_macros::context]
impl<T: Copy + thrust_models::Model> Iter for Rep<T> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        Some(self.v)
    }
}

#[thrust_macros::requires(<Rep<isize> as Iter>::produces(*r, x) ==> x == 0)]
fn client(r: &Rep<isize>, x: isize) {} //~ ERROR: the derived predicate

fn main() {}

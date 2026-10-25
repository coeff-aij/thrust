//@compile-flags: -C debug-assertions=off -A unused-variables -A dead_code
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// Rejected. `#[thrust_macros::predicate(derived)]` on an impl's item rather than the trait's.

#[thrust_macros::context]
trait Iter {
    #[thrust_macros::predicate(derived)]
    fn produces(self, item: isize) -> bool;
    #[thrust_macros::ensures(thrust_models::forall(|i| result == Some(i) ==> Self::produces(*self, i)))]
    fn next(&mut self) -> Option<isize>;
}

#[derive(PartialEq)]
struct R { s: isize }
impl thrust_models::Model for R { type Ty = R; }

#[thrust_macros::context]
impl Iter for R {
    #[thrust_macros::predicate(derived)] //~ ERROR: `#[thrust_macros::predicate(derived)]` declares
    fn produces(self, item: isize) -> bool;

    fn next(&mut self) -> Option<isize> { Some(self.s) }
}

fn main() { let mut r = R { s: 0 }; let _ = r.next(); }

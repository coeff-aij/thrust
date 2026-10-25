//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -Adead_code -Aunused
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A generic caller at `T := Even` calls an impl method that assumes the invariant, with an odd
// value.
#[derive(Clone, Copy)]
struct Even(i64);
impl thrust_models::Model for Even { type Ty = Self; }
#[thrust_macros::context]
impl Invariant for Even {
    #[thrust_macros::predicate]
    fn invariant(self) -> bool { self.0 % 2 == 0 }
}
trait Tr { fn m(self); }
impl Tr for Even { fn m(self) { assert!(self.0 % 2 == 0); } }
fn h<T: Tr>(t: T) { t.m() }
fn main() { h(Even(1)); }

//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -Adead_code -Aunused
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// As `generic_impl.rs`, with the impl method's own written contract: the invariant is part of it.
#[derive(Clone, Copy)]
struct Even(i64);
impl thrust_models::Model for Even { type Ty = Self; }
#[thrust_macros::context]
impl Invariant for Even {
    #[thrust_macros::predicate]
    fn invariant(self) -> bool { self.0 % 2 == 0 }
}
#[thrust_macros::context]
trait Tr: Sized {
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(true)]
    fn m(self);
}
#[thrust_macros::context]
impl Tr for Even {
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(true)]
    fn m(self) { assert!(self.0 % 2 == 0); }
}
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn h<T: Tr>(t: T) { t.m() }
fn main() { h(Even(1)); }

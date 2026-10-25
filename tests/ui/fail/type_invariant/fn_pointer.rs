//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -Adead_code -Aunused
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A function that assumes the invariant is called through a function pointer with an odd value.
#[derive(Clone, Copy)]
struct Even(i64);
impl thrust_models::Model for Even { type Ty = Self; }
#[thrust_macros::context]
impl Invariant for Even {
    #[thrust_macros::predicate]
    fn invariant(self) -> bool { self.0 % 2 == 0 }
}
fn check(e: Even) { assert!(e.0 % 2 == 0); }
fn call(f: fn(Even), x: i64) { f(Even(x)) }
fn main() { call(check, 1); }

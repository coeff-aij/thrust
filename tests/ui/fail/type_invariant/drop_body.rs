//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -Adead_code -Aunused
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A destructor takes no precondition (D57), the type invariant included: code Thrust does not
// analyze may drop an odd `Even`.
struct Even(i64);
impl thrust_models::Model for Even { type Ty = Self; }
#[thrust_macros::context]
impl Invariant for Even {
    #[thrust_macros::predicate]
    fn invariant(self) -> bool { self.0 % 2 == 0 }
}
impl Drop for Even { fn drop(&mut self) { assert!(self.0 % 2 == 0); } }
fn main() {}

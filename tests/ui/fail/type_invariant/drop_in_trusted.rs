//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -Adead_code -Aunused
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A trusted function that takes an odd `Even` (`open_inv`) drops it, running the destructor.
struct Even(i64);
impl thrust_models::Model for Even { type Ty = Self; }
#[thrust_macros::context]
impl Invariant for Even {
    #[thrust_macros::predicate]
    fn invariant(self) -> bool { self.0 % 2 == 0 }
}
impl Drop for Even { fn drop(&mut self) { assert!(self.0 % 2 == 0); } }
#[thrust::trusted]
#[thrust::callable]
fn sink(#[thrust::open_inv] e: Even) {}
fn main() { sink(Even(1)); }

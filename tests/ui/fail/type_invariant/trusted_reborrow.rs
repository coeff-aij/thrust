//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -Adead_code -Aunused
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A trusted function returns a reborrow of its `&mut Even` parameter, and the caller writes an odd
// value through it. The final value of a borrow the result holds is set by the caller, so the
// invariant is not ensured of it.
#[derive(Clone, Copy)]
struct Even(i64);
impl thrust_models::Model for Even { type Ty = Self; }
#[thrust_macros::context]
impl Invariant for Even {
    #[thrust_macros::predicate]
    fn invariant(self) -> bool { self.0 % 2 == 0 }
}
#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(*result == *x && !result == !x)]
fn as_mut(x: &mut Even) -> &mut Even { x }
fn main() {
    let mut e = Even(0);
    { let r = as_mut(&mut e); r.0 = 1; }
    assert!(1 == 2);
}

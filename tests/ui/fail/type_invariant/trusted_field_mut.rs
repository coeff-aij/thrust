//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -Adead_code -Aunused
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A trusted accessor returns a `&mut` to a field of its `&mut Even` parameter, and the caller
// writes an odd value through it: the invariant is not ensured of the parameter's final value.
#[derive(Clone, Copy)]
struct Even(i64);
impl thrust_models::Model for Even { type Ty = Self; }
#[thrust_macros::context]
impl Invariant for Even {
    #[thrust_macros::predicate]
    fn invariant(self) -> bool { self.0 % 2 == 0 }
}
#[thrust::trusted]
#[thrust::callable]
fn field_mut(e: &mut Even) -> &mut i64 { &mut e.0 }
fn main() {
    let mut e = Even(0);
    { let r = field_mut(&mut e); *r = 1; }
    assert!(e.0 % 2 == 0);
}

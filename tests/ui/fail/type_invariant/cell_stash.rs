//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -Adead_code -Aunused
//@rustc-env: THRUST_UNSPECIFIED_UNREACHABLE=1 THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A trusted function stores the borrow of its `&mut Even` parameter in a `Cell` named by a shared
// parameter of the same lifetime, and another hands it back to the caller, who writes an odd value:
// the borrow outlives the call, so the invariant is not ensured of the parameter's final value.
#[derive(Clone, Copy)]
struct Even(i64);
impl thrust_models::Model for Even { type Ty = Self; }
#[thrust_macros::context]
impl Invariant for Even {
    #[thrust_macros::predicate]
    fn invariant(self) -> bool { self.0 % 2 == 0 }
}
use std::cell::Cell;

#[thrust::trusted]
#[thrust::callable]
fn stash<'a>(x: &'a mut Even, c: &Cell<Option<&'a mut Even>>) {
    c.set(Some(x));
}

#[thrust::trusted]
#[thrust::callable]
fn take<'a>(c: &Cell<Option<&'a mut Even>>) -> &'a mut i64 {
    &mut c.take().unwrap().0
}

fn main() {
    let mut e = Even(0);
    {
        let c = Cell::new(None);
        stash(&mut e, &c);
        let r = take(&c);
        *r = 1;
    }
    assert!(e.0 % 2 == 0);
}

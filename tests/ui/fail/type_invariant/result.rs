//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A result breaks the invariant: `new_even` is checked against it at its exit.
struct Even(i64);

impl thrust_models::Model for Even {
    type Ty = Self;
}

#[thrust_macros::context]
impl Invariant for Even {
    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        self.0 % 2 == 0
    }
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn new_even() -> Even {
    Even(1)
}

// Breaks the invariant between its entry and its exit.
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn bump(e: &mut Even) {
    e.0 += 1;
    e.0 += 1;
}

// The invariant is assumed of `*e`.
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result % 2 == 0)]
fn get(e: &Even) -> i64 {
    e.0
}

// Takes an `Even` that may break the invariant and restores it, which its `ensures` states.
#[thrust_macros::requires(true)]
#[thrust_macros::ensures((!e).0 % 2 == 0)]
fn fix(#[thrust::open_inv] e: &mut Even) {
    if e.0 % 2 != 0 {
        e.0 = 0;
    }
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
#[thrust::open_inv_result]
fn odd() -> Even {
    Even(1)
}

// Without a contract: the invariant is part of the inferred contract.
fn make(k: i64) -> Even {
    Even(k * 2)
}

fn twice(e: &Even) -> i64 {
    assert!(e.0 % 2 == 0);
    e.0
}

fn main() {
    let mut e = new_even();
    bump(&mut e);
    assert!(get(&e) % 2 == 0);

    let mut o = odd();
    fix(&mut o);
    assert!(get(&o) % 2 == 0);

    let m = make(3);
    twice(&m);
}

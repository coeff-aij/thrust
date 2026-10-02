//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

use thrust_models::{exists, forall, model::{Closure, Mut}};

// Verified once over `F` from the laws of `hist_inv!` (each call's postcondition implies it, and
// transitivity), and the call in `main` uses the contract as instantiated once the closure is
// shown to obey those laws. The contract hides the state between the calls.
#[thrust_macros::requires(forall(|c: Closure<F>, y: i64| thrust_macros::pre!(c(y))))]
#[thrust_macros::ensures(thrust_macros::hist_inv!(*f, !f))]
#[thrust_macros::ensures(exists(|g, y: i64|
    thrust_macros::hist_inv!(*f, g) && thrust_macros::post!(Mut::new(g, !f)(y), result)))]
fn apply_twice<F: FnMut(i64) -> i64>(f: &mut F, x: i64) -> i64 {
    let y = f(x);
    f(y)
}

fn main() {
    let mut cnt: i64 = 0;
    // The contract does not say that the call keeps the capture's prophecy: the postcondition
    // the closure is checked against and callers use includes it, as Creusot's
    // `postcondition_mut` includes `hist_inv(self, ^self)`.
    let mut c = thrust_macros::closure!(
        captures(cnt: &mut &mut i64),
        requires(true),
        ensures(*(!cnt) == 7 && result == x),
        |x: i64| -> i64 {
            cnt = 7;
            x
        },
    );
    apply_twice(&mut c, 1);
    // `cnt` is 7
    assert!(cnt == 8);
}


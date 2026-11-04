//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
use thrust_models::{exists, forall, model::{Closure, Mut}};

// `check`'s `hist_inv` clause relates its states through `P`'s, which carries `check`'s history
// to `wrap`'s postcondition. The argument borrows its counter by `&mut`, its `hist_inv` clause
// states that the counter never decreases, and its contract is left to inference, so `wrap` is
// analyzed again at it, with the relation of `P` there. Two calls leave the counter at 2, so
// `wrap`'s result is 2 and the assertion that it is at least 3 is refuted.
#[thrust_macros::context]
#[thrust_macros::requires(forall(|c: Closure<P>| thrust_macros::pre!(c())))]
#[thrust_macros::ensures(exists(|c: Closure<P>, d: Closure<P>|
    thrust_macros::hist_inv!(p, c) && thrust_macros::post!(Mut::new(c, d)(), result)))]
fn wrap<P: FnMut() -> i64>(mut p: P) -> i64 {
    let mut check = thrust_macros::closure!(
        captures(p: &mut P),
        hist_inv(thrust_macros::hist_inv!(*p, !p)),
        move || -> i64 { p() },
    );
    check();
    check()
}

fn main() {
    let mut n: i64 = 0;
    let r = wrap(thrust_macros::closure!(
        captures(n: &mut &mut i64),
        hist_inv(**n <= *!n),
        || -> i64 {
            n += 1;
            n
        },
    ));
    assert!(r >= 3);
}

//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

use thrust_models::{exists, model::Mut};

// `call_twice` hides the state between the calls, so the caller learns the final value of
// `cnt` only through `unnest!`, which at this closure keeps the borrow's prophecy.
#[thrust_macros::ensures(exists(|g|
    thrust_macros::unnest!(*f, g) && thrust_macros::post!(Mut::new(g, !f)(), ())))]
fn call_twice<F: FnMut()>(f: &mut F) {
    f();
    f();
}

fn main() {
    let mut cnt: i64 = 0;
    let mut c = thrust_macros::closure!(
        captures(cnt: &mut &mut i64),
        ensures(*(!cnt) == 7),
        ensures(!(!cnt) == !(*cnt)),
        || -> () { cnt = 7; },
    );
    call_twice(&mut c);
    assert!(cnt == 8);
}

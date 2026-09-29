//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:0360cb142 THRUST_FNMUT_GENERIC=1
use thrust_models::{exists, model::Mut};

// With THRUST_FNMUT_GENERIC, `call` is used at its generic analysis, and the precondition
// clause rejects the closure's precondition, which reads the exit slot of its receiver.

#[thrust_macros::requires(thrust_macros::pre!(f()))]
#[thrust_macros::ensures(exists(|g| thrust_macros::post!(Mut::new(f, g)(), result)))]
fn call<F: FnMut() -> i64>(mut f: F) -> i64 {
    f()
}

fn main() {
    let mut cnt: i64 = 0;
    // The precondition says the call leaves the counter unchanged, which the body contradicts:
    // the closure verifies vacuously, and a direct call would have to prove it of a prophecy.
    let f = thrust_macros::closure!(
        captures(cnt: &mut &mut i64),
        requires(*(!cnt) == *(*cnt)),
        ensures(result == 100),
        || -> i64 {
            cnt += 1;
            cnt
        },
    );
    let r = call(f);
    // `f` returns 1
    assert!(r == 100);
}

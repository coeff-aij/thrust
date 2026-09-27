//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:develop-2493045c3
use thrust_models::{exists, model::Mut};

#[thrust_macros::requires(thrust_macros::pre!(f()))]
#[thrust_macros::ensures(exists(|g| thrust_macros::post!(Mut::new(f, g)(), result)))]
fn call<F: FnMut() -> i64>(mut f: F) -> i64 {
    f()
}

fn main() {
    let mut cnt: i64 = 0;
    // The precondition reads only the counter's entry value, so the instance of `call`'s contract
    // agrees with the generic one.
    let f = thrust_macros::closure!(
        captures(cnt: &mut &mut i64),
        requires(*(*cnt) == 0),
        ensures(result == *(*cnt) + 1),
        || -> i64 {
            cnt += 1;
            cnt
        },
    );
    let r = call(f);
    // `f` returns 1
    assert!(r == 1);
}

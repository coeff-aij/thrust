//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The temporaries of an annotated `for` head live as long as the loop, as in rustc's lowering:
// `make().iter()` borrows the vector `make` returns.
// Fail twin: the vector's item is 1.

fn make() -> Vec<i64> {
    let mut v = Vec::new();
    v.push(1);
    v
}

#[thrust_macros::context]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn f() {
    for x in make().iter() {
        thrust_macros::invariant!(|iter: core::slice::Iter<'_, i64>, iter_old: thrust_models::Ghost<core::slice::Iter<'_, i64>>| true);
        let _ = x;
        assert!(*x == 2);
    }
}

fn main() {}

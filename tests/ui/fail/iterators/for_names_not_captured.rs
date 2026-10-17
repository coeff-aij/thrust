//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The `for` desugaring's own variables do not capture the body's: `iter` in the body is the
// function's, while the invariant's `iter` is the loop's iterator.
// Fail twin: the function's `iter` is 5.

#[thrust_macros::context]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn f(v: &Vec<i64>) {
    let iter: i64 = 5;
    for _x in v.iter() {
        thrust_macros::invariant!(|iter: core::slice::Iter<'_, i64>, iter_old: thrust_models::Ghost<core::slice::Iter<'_, i64>>| true);
        assert!(iter + 1 == 7);
    }
}

fn main() {}

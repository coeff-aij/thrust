//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// An annotated `for` inside another `for` names its own iterator, apart from the outer loop's.
// Fail twin: the vector's items may be negative.

#[thrust_macros::context]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn f(v: &Vec<i64>) {
    for _i in 0..2i64 {
        for x in v.iter() {
            thrust_macros::invariant!(|iter: core::slice::Iter<'_, i64>, iter_old: thrust_models::Ghost<core::slice::Iter<'_, i64>>| true);
            let _ = x;
            assert!(*x > 0);
        }
    }
}

fn main() {}

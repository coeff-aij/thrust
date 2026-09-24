//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60 COAR_IMAGE=coar:develop-2493045c3

// The whole-ADT comparison against the entry state tracks the entry value, not the
// current one: the loop raises `lo`, so the current bounds leave the entry bounds behind.

use thrust_models::model::{Int, Seq};
use thrust_models::Ghost;

#[derive(PartialEq)]
struct Bounds {
    lo: i64,
    hi: i64,
}

impl thrust_models::Model for Bounds {
    type Ty = Bounds;
}

struct Walk {
    bounds: Bounds,
    seen: Ghost<Seq<Int>>,
}

impl thrust_models::Model for Walk {
    type Ty = (Bounds, Seq<Int>);
}

#[thrust_macros::context]
#[thrust_macros::requires((*w).0.lo == 3 && (*w).0.hi == 9 && (*w).1.len() == 0 && n >= 0)]
fn walk_upto(w: &mut Walk, n: i64) {
    let ww = w;
    let mut i = 0;
    while i < n {
        thrust_macros::invariant!(
            |ww: &mut Walk, w: thrust_models::FnParam<&mut Walk>, i: i64, n: i64|
            0 <= i
                && i <= n
                && (*ww).1.len() == i
                && (*ww).0 == (*w.at_entry()).0
                && (*w.at_entry()).0.lo == 3
                && (*w.at_entry()).0.hi == 9
        );
        ww.bounds.lo += 1;
        ww.seen = thrust_macros::ghost!(|ww: &mut Walk, i: i64| -> Seq<Int> { (*ww).1.push(i) });
        i += 1;
    }
}

fn main() {}

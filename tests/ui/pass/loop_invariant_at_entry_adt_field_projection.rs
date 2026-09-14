//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables

// An ADT-typed field of a `&mut` parameter's entry state survives `at_entry()`: it can
// be compared whole against the current local, and projected into for the concrete
// values the loop body needs.

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
        ww.seen = thrust_macros::ghost!(|ww: &mut Walk, i: i64| -> Seq<Int> { (*ww).1.push(i) });
        i += 1;
    }
}

fn main() {}

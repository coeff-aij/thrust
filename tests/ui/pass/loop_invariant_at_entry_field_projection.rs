//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables

// A loop invariant may name individual fields of a `&mut` parameter's entry state
// through `at_entry()`, without also asserting a whole-value equality against it.

use thrust_models::model::{Int, Seq};
use thrust_models::Ghost;

struct Recorder {
    count: i64,
    hist: Ghost<Seq<Int>>,
}

impl thrust_models::Model for Recorder {
    type Ty = (Int, Seq<Int>);
}

#[thrust_macros::context]
#[thrust_macros::requires((*r).0 == 7 && (*r).1.len() == 0 && n >= 0)]
fn record_upto(r: &mut Recorder, n: i64) {
    let rr = r;
    let mut i = 0;
    while i < n {
        thrust_macros::invariant!(
            |rr: &mut Recorder, r: thrust_models::FnParam<&mut Recorder>, i: i64, n: i64|
            0 <= i
                && i <= n
                && (*rr).1.len() == i
                && (*r.at_entry()).0 == 7
                && (*r.at_entry()).1.len() == 0
        );
        rr.hist = thrust_macros::ghost!(|rr: &mut Recorder, i: i64| -> Seq<Int> { (*rr).1.push(i) });
        rr.count += 1;
        i += 1;
    }
}

fn main() {}

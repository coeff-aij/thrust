//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:develop-2493045c3

use thrust_models::model::{Int, Seq};
use thrust_models::{Ghost, Model};

struct Hist {
    produced: Ghost<Seq<Int>>,
}

impl Model for Hist {
    type Ty = Hist;
}

#[thrust_macros::ensures((!h).produced == (*h).produced.push(x + 1))]
fn bump(h: &mut Hist, x: i64) {
    h.produced =
        thrust_macros::ghost!(|h: &mut Hist, x: i64| -> Seq<Int> { (*h).produced.push(x) });
}

#[thrust_macros::requires((*h).produced.len() == 2 && (*h).produced[1] == 2)]
fn expect_two(h: &Hist) {
    let _ = h;
}

fn main() {
    let mut h = Hist {
        produced: thrust_macros::ghost!(|| -> Seq<Int> { Seq::empty() }),
    };
    bump(&mut h, 1);
    bump(&mut h, 2);
    expect_two(&h);
}

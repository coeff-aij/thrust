use thrust_models::model::{Int, Seq};
use thrust_models::{Ghost, Model};

struct Hist {
    produced: Ghost<Seq<Int>>,
}

impl Model for Hist {
    type Ty = Hist;
}

fn bump(h: &mut Hist, x: i64) {
    h.produced = thrust_macros::ghost!(|h: Hist, x: i64| -> Seq<Int> { h.produced.push(x) });
}

fn main() {
    let mut h = Hist {
        produced: thrust_macros::ghost!(|| -> Seq<Int> { Seq::empty() }),
    };
    bump(&mut h, 1);
}

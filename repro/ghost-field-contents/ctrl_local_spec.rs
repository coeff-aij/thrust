use thrust_models::model::{Int, Seq};
use thrust_models::{Ghost, Model};

struct Hist {
    produced: Ghost<Seq<Int>>,
}

impl Model for Hist {
    type Ty = Hist;
}

#[thrust_macros::ensures((!h).produced == (*h).produced.push(x))]
fn bump(h: &mut Hist, x: i64) {
    let p = h.produced;
    h.produced = thrust_macros::ghost!(|p: Ghost<Seq<Int>>, x: i64| -> Seq<Int> { p.push(x) });
}

fn main() {
    let mut h = Hist {
        produced: thrust_macros::ghost!(|| -> Seq<Int> { Seq::empty() }),
    };
    bump(&mut h, 1);
}

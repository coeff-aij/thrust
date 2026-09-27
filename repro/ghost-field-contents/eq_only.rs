use thrust_models::model::{Int, Seq};
use thrust_models::{Ghost, Model};

struct Hist {
    produced: Ghost<Seq<Int>>,
}
impl Model for Hist {
    type Ty = Hist;
}

#[thrust_macros::ensures((!h).produced == (*h).produced)]
fn bump(h: &mut Hist, x: i64) {
    let _ = x;
}

fn main() {
    let mut h = Hist {
        produced: thrust_macros::ghost!(|| -> Seq<Int> { Seq::empty() }),
    };
    bump(&mut h, 1);
}

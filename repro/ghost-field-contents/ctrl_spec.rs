use thrust_models::model::{Int, Seq};
use thrust_models::{Ghost, Model};

struct Hist {
    produced: Ghost<Seq<Int>>,
}
impl Model for Hist {
    type Ty = Hist;
}

#[thrust_macros::ensures(result == produced.push(x))]
fn push_produced(produced: Ghost<Seq<Int>>, x: i64) -> Ghost<Seq<Int>> {
    thrust_macros::ghost!(|produced: Ghost<Seq<Int>>, x: i64| -> Seq<Int> { produced.push(x) })
}

#[thrust_macros::ensures((!h).produced == (*h).produced.push(x))]
fn bump(h: &mut Hist, x: i64) {
    h.produced = push_produced(h.produced, x);
}

fn main() {
    let mut h = Hist {
        produced: thrust_macros::ghost!(|| -> Seq<Int> { Seq::empty() }),
    };
    bump(&mut h, 1);
}

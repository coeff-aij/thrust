//@compile-flags: -C debug-assertions=off -A unused-variables

// rustc checks that a `match` in a formula is exhaustive, in an `ensures`, a logic function's
// body and a ghost term alike. A `match` of a non-Boolean type relies on it: its last arm is the
// value where no earlier arm matches, and the selectors it reads are read under their testers
// only because its pattern then holds.
use thrust_models::model::{Int, Seq};
use thrust_models::Ghost;

enum Shape {
    Circle(i64),
    Rect { w: i64, h: i64 },
    Empty,
}

impl thrust_models::Model for Shape {
    type Ty = Self;
}

#[thrust_macros::logic]
fn widen(s: Shape) -> Shape {
    match s { //~ ERROR: non-exhaustive patterns
        Shape::Circle(r) => Shape::Circle(r),
        Shape::Rect { w, h } => Shape::Circle(w),
    }
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == match s { Shape::Circle(r) => r, Shape::Rect { w, h } => w })] //~ ERROR: non-exhaustive patterns
fn size(s: Shape) -> i64 {
    42
}

fn record(r: Option<i64>) {
    let empty = thrust_macros::ghost!(|| -> Seq<Int> { Seq::empty() });
    let pushed = thrust_macros::ghost!(|empty: Ghost<Seq<Int>>, r: Option<i64>| -> Seq<Int> {
        match r { //~ ERROR: non-exhaustive patterns
            Some(x) => empty.push(x),
        }
    });
}

fn main() {}

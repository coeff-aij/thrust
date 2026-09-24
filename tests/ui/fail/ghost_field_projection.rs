//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables

use thrust_models::{Ghost, Model};

#[derive(Clone, Copy, PartialEq)]
struct Point {
    x: i64,
}

impl Model for Point {
    type Ty = Point;
}

struct Tracker {
    last: Ghost<Point>,
}

impl Model for Tracker {
    type Ty = Tracker;
}

#[thrust_macros::ensures((!t).last.x == (*t).last.x + 2)]
fn shift(t: &mut Tracker) {
    t.last = thrust_macros::ghost!(|t: &mut Tracker| -> Point {
        Point { x: (*t).last.x + 1 }
    });
}

fn main() {}

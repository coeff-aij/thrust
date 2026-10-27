//@compile-flags: -C debug-assertions=off

// The types an invariant of a `for` gives `iter`, `iter_old` and `produced` are compared with the
// iterator's as they are, without the coercion through `Deref` that `W` admits.

use std::ops::{Deref, Range};
use thrust_models::model::Seq;
use thrust_models::Ghost;

struct W {
    r: Range<i64>,
}

impl Deref for W {
    type Target = Range<i64>;
    fn deref(&self) -> &Range<i64> {
        &self.r
    }
}

impl Iterator for W {
    type Item = i64;
    fn next(&mut self) -> Option<i64> {
        self.r.next()
    }
}

#[thrust_macros::context]
fn iter_through_deref(n: i64) {
    for _ in (W { r: 0..n }) {
        thrust_macros::invariant!(|iter: Range<i64>| iter.start >= 0); //~ ERROR: mismatched types
    }
}

#[thrust_macros::context]
fn iter_old_without_ghost(n: i64) {
    for _ in 0..n {
        thrust_macros::invariant!(|iter: Range<i64>, iter_old: Range<i64>| iter_old.start <= iter.start); //~ ERROR: mismatched types
    }
}

#[thrust_macros::context]
fn produced_of_other_items(n: i64) {
    for _ in 0..n {
        thrust_macros::invariant!(|iter: Range<i64>, produced: Ghost<Seq<bool>>| produced.len() >= 0); //~ ERROR: mismatched types
    }
}

fn main() {}

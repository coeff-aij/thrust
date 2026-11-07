//@compile-flags: -C debug-assertions=off -A unused

// An invariant of a `for` loop that names the history `produced` or `iter_old` also names the
// loop's iterator `iter` with its type, from which the ghosts take their types.

use thrust_models::model::{Int, Seq};
use thrust_models::Ghost;

#[thrust_macros::context]
fn produced_only(n: i64) {
    let mut s = 0;
    for i in 0..n { //~ ERROR: a loop invariant that names `iter_old` or `produced` also names `iter`
        thrust_macros::invariant!(|produced: Ghost<Seq<Int>>, s: i64| s >= 0);
        s += 1;
    }
}

fn main() {}

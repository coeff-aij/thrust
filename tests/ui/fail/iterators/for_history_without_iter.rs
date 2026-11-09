//@error-in-other-file: in a function under `#[thrust_macros::context]`, a `for` loop's ghost history is introduced only when the invariant also names the loop's iterator as `iter` with its type
//@compile-flags: -C debug-assertions=off -A unused

// An invariant of a `for` loop that names the history `produced` without the loop's iterator
// `iter`: the loop is not desugared, no variable `produced` is live, and the error says why.

use thrust_models::model::{Int, Seq};
use thrust_models::Ghost;

#[thrust_macros::context]
fn produced_only(n: i64) {
    let mut s = 0;
    for i in 0..n {
        thrust_macros::invariant!(|produced: Ghost<Seq<Int>>, s: i64| s >= 0);
        s += 1;
    }
}

fn main() {}

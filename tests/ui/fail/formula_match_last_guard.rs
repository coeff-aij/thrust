//@compile-flags: -C debug-assertions=off -A unused-variables -A unreachable-patterns

// A `match` of a non-Boolean type in a formula takes its last arm where no earlier arm matches,
// so that arm cannot have a guard, as in Verus: here rustc accepts it as unreachable.
use thrust_models::model::{Int, Seq};
use thrust_models::Ghost;

fn record(r: Option<i64>) {
    let empty = thrust_macros::ghost!(|| -> Seq<Int> { Seq::empty() });
    let pushed = thrust_macros::ghost!(|empty: Ghost<Seq<Int>>, r: Option<i64>| -> Seq<Int> {
        match r {
            None => empty,
            Some(x) => empty.push(x),
            Some(x) if x > 0 => empty, //~ ERROR: a guard on the last arm
        }
    });
}

fn main() {}

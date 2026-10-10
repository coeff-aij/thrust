//@compile-flags: -Adead_code -C debug-assertions=off

// A variant that calls the function it measures could be discharged by the inconsistency of
// the function's own definition when it does not terminate.
#[thrust_macros::logic] //~ ERROR: a predicate or logic function is called from a function or variant it calls
#[thrust_macros::variant(bad(x, y))]
fn bad(x: i64, y: i64) -> i64 {
    if x == y {
        bad(y, x) + 1
    } else {
        0
    }
}

#[thrust_macros::requires(x == y)]
#[thrust_macros::ensures(bad(x, y) == 5 && bad(x, y) == 6)]
fn f(x: i64, y: i64) {}

fn main() {
    f(0, 0);
}

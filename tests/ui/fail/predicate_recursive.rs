//@compile-flags: -Adead_code -C debug-assertions=off

// A recursive predicate has no variant to show that it terminates, and its `define-fun-rec`
// would be inconsistent.
#[thrust_macros::predicate]
fn liar(x: i64) -> bool {
    !liar(x) //~ ERROR: a predicate cannot call itself
}

#[thrust_macros::ensures(liar(x))]
fn f(x: i64) {}

fn main() {
    f(0);
}

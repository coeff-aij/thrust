//@compile-flags: -C debug-assertions=off -A unused-variables

// A `&str` has no `Model`, so a specification cannot compare two: `result != a` would be false
// of every pair and make the code after the call vacuous.
#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result != a)] //~ ERROR: the trait bound `str: thrust_models::Model` is not satisfied
//~^ ERROR: the method `log_ne` exists
fn different(a: &'static str) -> &'static str { //~ ERROR: the trait bound `str: thrust_models::Model` is not satisfied
    if a == "x" { "y" } else { "x" }
}

fn main() {
    let _ = different("x");
    assert!(1 == 2);
}

//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// `#[thrust::assumed_ensures]` keeps the precondition: a call outside it fails.
#[thrust::assumed_ensures]
#[thrust_macros::requires(x >= 0 && x < 100)]
#[thrust_macros::ensures(result == x + 1)]
fn add_one(x: i64) -> i64 {
    x + 1
}

fn main() {
    let y = add_one(-1);
    assert!(y == 0);
}

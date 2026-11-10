//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// `#[thrust::assumed_ensures]` assumes only the postcondition: the rest of the body is checked,
// here the assertion that fails at `x == 0`.
#[thrust::assumed_ensures]
#[thrust_macros::requires(x >= 0 && x < 100)]
#[thrust_macros::ensures(result == x + 1)]
fn add_one(x: i64) -> i64 {
    assert!(x > 0);
    x + 1
}

fn main() {
    let y = add_one(1);
    assert!(y == 2);
}

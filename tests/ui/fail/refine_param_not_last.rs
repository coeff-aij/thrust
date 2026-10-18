//@error-in-other-file: Unsat

#[thrust_macros::param(x: { v: i64 | v >= -1 })]
fn f(x: i64, y: i64) {
    assert!(x >= 0);
}

fn main() {}

//@check-pass

#[thrust_macros::param(x: { v: i64 | v >= 0 })]
fn f(x: i64, y: i64) {
    assert!(x >= 0);
}

fn main() {}

//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

#[derive(Debug)]
struct Point {
    x: i64,
    y: i64,
}

#[thrust_macros::requires(x > 0)]
fn display(x: i64) -> i64 {
    if x <= 0 {
        panic!("not positive: {}", x);
    }
    x - 1
}

#[thrust_macros::requires(x > 0)]
fn assert_message(x: i64) {
    assert!(x > 0, "x = {x}");
}

#[thrust_macros::requires(x < y)]
fn debug(x: i64, y: i64) -> i64 {
    let p = Point { x, y };
    if p.x >= p.y {
        unreachable!("unordered: {p:?}");
    }
    p.y - p.x
}

fn main() {}

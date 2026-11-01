//@check-pass
//@compile-flags: -C debug-assertions=off

#[thrust_macros::predicate]
fn positive(x: i32) -> bool {
    x > 0
}

#[thrust_macros::requires(positive(x) == positive(y))]
#[thrust_macros::ensures(if positive(x) { positive(result) } else { !positive(result) })]
fn larger(x: i32, y: i32) -> i32 {
    if x > y {
        x
    } else {
        y
    }
}

fn main() {
    assert!(larger(1, 2) > 0);
}

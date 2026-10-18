//@check-pass
//@compile-flags: -C debug-assertions=off

#[thrust_macros::param(x: &mut { v: i64 | v >= 0 })]
fn set_first(x: &mut i64, y: &mut i64) {
    *x = 1;
    *y = -1;
}

#[thrust_macros::param(y: &mut { v: i64 | v >= 0 })]
fn set_second(x: &mut i64, y: &mut i64) {
    *x = -1;
    *y = 1;
}

fn main() {}

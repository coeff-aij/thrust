//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

#[thrust_macros::param(x: &mut { v: i64 | v >= 0 })]
fn set_first(x: &mut i64, y: &mut i64, z: &mut i64) {
    *x = 1;
    *y = -1;
    *z = -1;
}

#[thrust_macros::param(y: &mut { v: i64 | v >= 0 })]
fn set_middle(x: &mut i64, y: &mut i64, z: &mut i64) {
    *x = -1;
    *y = -1;
    *z = -1;
}

#[thrust_macros::param(z: &mut { v: i64 | v >= 0 })]
fn set_last(x: &mut i64, y: &mut i64, z: &mut i64) {
    *x = -1;
    *y = -1;
    *z = 1;
}

fn main() {}

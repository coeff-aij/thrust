#[thrust_macros::param(x: &mut { v: i64 | v >= 0 })]
fn set(x: &mut i64) {
    *x = -1;
}

fn main() {
    let mut a = 1;
    set(&mut a);
}

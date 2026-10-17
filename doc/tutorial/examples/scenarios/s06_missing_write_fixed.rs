#[thrust_macros::ensures(!a == *b && !b == *a)]
fn swap(a: &mut i64, b: &mut i64) {
    let t = *a;
    *a = *b;
    *b = t;
}

fn main() {
    let mut x = 1;
    let mut y = 2;
    swap(&mut x, &mut y);
    assert!(x == 2 && y == 1);
}

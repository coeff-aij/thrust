#[thrust_macros::ensures(!r == *r + a)]
fn add_to(r: &mut i64, a: i64) {
    *r += a;
}

fn main() {
    let mut x = 1;
    add_to(&mut x, 2);
    assert!(x == 3);
}

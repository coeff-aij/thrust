fn swap(x: &mut i64, y: &mut i64) {
    *x = *y;
}

fn main() {
    let mut a = 1;
    let mut b = 3;
    swap(&mut a, &mut b);
    assert!(b == 1);
}

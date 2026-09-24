fn main() {
    let mut a = [1i32, 2, 3, 4];
    let i = 2;
    a[i] = 5;
    assert!(a[i] == 5);
}

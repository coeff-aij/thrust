fn main() {
    let mut a = 1;
    let old = std::mem::replace(&mut a, 2);
    assert!(old == 2);
}

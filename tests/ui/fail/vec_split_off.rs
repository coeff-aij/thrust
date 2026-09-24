//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

fn main() {
    let mut a: Vec<i32> = Vec::new();
    Vec::push(&mut a, 1);
    Vec::push(&mut a, 2);
    let b = a.split_off(1);
    assert!(a.len() == 1);
    assert!(b.len() == 2);
}

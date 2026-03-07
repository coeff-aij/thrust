//@check-pass
//@compile-flags: -C debug-assertions=off

fn main() {
    let mut i = -5;
    while i != 0 {
        i -= 1;
    }
    assert!(i == 0); // Thrust guarantees only partial correctness.
}

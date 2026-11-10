//@check-pass
//@compile-flags: -C debug-assertions=off

// std.rs's `mem::take` at an integer type returns the value and leaves 0.

fn main() {
    let mut x: u64 = 42;
    let old = std::mem::take(&mut x);
    assert!(old == 42);
    assert!(x == 0);
}

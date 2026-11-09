//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// The twin of `pass/std_mem_take_int.rs`: the integer is 0 after the take, not its old value.

fn main() {
    let mut x: u64 = 42;
    let old = std::mem::take(&mut x);
    assert!(x == 42);
}

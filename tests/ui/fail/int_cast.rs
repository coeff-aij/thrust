//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

fn widen(x: u32) -> u64 {
    x as u64
}

fn narrow(x: usize) -> u32 {
    x as u32
}

fn resign(x: i64) -> u128 {
    x as u128
}

fn main() {
    let a: u32 = 7;
    assert!(widen(a) == 8);
    assert!(narrow(7) == 7);
    assert!(resign(7) == 7);
}

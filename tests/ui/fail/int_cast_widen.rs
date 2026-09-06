//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

fn to_u64(x: u32) -> u64 {
    x as u64
}

fn to_i64(x: i32) -> i64 {
    x as i64
}

fn u32_to_i64(x: u32) -> i64 {
    x as i64
}

fn main() {
    assert!(to_u64(2147483647) == 2147483647);
    assert!(to_i64(-2147483648) == -2147483647);
    assert!(u32_to_i64(2147483647) == 2147483647);
}

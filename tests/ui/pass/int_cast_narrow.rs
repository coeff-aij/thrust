//@check-pass
//@compile-flags: -C debug-assertions=off

fn to_u32(x: i64) -> u32 {
    x as u32
}

fn to_i32(x: u64) -> i32 {
    x as i32
}

// The `as u64` is a value-preserving widening; it only lets `main` compare the
// wrapped result against a literal that is not itself a large `u32` constant.
fn i32_to_u32(x: i32) -> u64 {
    (x as u32) as u64
}

fn main() {
    assert!(to_u32(4294967596) == 300);
    assert!(to_i32(4294967240) == -56);
    assert!(i32_to_u32(-1) == 4294967295);
}

//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// Every `char` is a Unicode scalar value: its code point is at most `0x10FFFF` and not a
// surrogate (`0xD800..=0xDFFF`). That holds of a parameter of any value and of `u8 as char`,
// whose operand has no upper bound here.

#[thrust::callable]
fn code_point(c: char) -> u32 {
    let n = c as u32;
    assert!(n <= 0xFFFF);
    assert!(n < 0xD800 || 0xDFFF < n);
    n
}

#[thrust::callable]
fn from_byte(x: u8) -> u32 {
    let n = x as char as u32;
    assert!(n <= 0x10FFFF);
    n
}

fn main() {}

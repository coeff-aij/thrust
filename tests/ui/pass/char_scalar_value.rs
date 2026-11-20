//@check-pass
//@compile-flags: -C debug-assertions=off

// Every `char` is a Unicode scalar value: its code point is at most `0x10FFFF` and not a
// surrogate (`0xD800..=0xDFFF`). That holds of a parameter and of `u8 as char`, whose operand has
// no upper bound here.

fn code_point(c: char) -> u32 {
    let n = c as u32;
    assert!(n <= 0x10FFFF);
    assert!(n < 0xD800 || 0xDFFF < n);
    n
}

fn from_byte(x: u8) -> u32 {
    let n = x as char as u32;
    assert!(n <= 0x10FFFF);
    n
}

fn main() {
    assert!(code_point('a') == 97);
    assert!(code_point(char::MAX) == 0x10FFFF);
    assert!(from_byte(200) == 200);
}

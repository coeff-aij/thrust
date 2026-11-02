//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// A `char` is the `u32` of its code point: `u8 as char` keeps the value, `c as u8` truncates it,
// and comparisons and patterns compare code points.

fn from_byte(x: u8) -> char {
    x as char
}

fn low_byte(c: char) -> u8 {
    c as u8
}

fn kind(c: char) -> i64 {
    match c {
        'a' => 1,
        'b'..='z' => 2,
        _ => 0,
    }
}

fn main() {
    assert!(from_byte(65) as u32 == 65);
    assert!(from_byte(65) == 'A');
    assert!(low_byte('\u{141}') == 0x42);
    assert!('a' < 'b');
    assert!(kind('a') == 1 && kind('q') == 2 && kind('A') == 0);
}

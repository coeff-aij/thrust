//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// `b as i64` and `b as u8` of a `bool` are 1 for `true` and 0 for `false`.

fn count(x: i64, y: i64) -> i64 {
    (x > 0) as i64 + (y > 0) as i64
}

fn flag(b: bool) -> u8 {
    b as u8
}

fn main() {
    assert!(count(1, -1) == 2);
    assert!(flag(true) == 1 && flag(false) == 0);
}

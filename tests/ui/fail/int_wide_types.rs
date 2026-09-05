//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

fn add_u8(x: u8, y: u8) -> u8 {
    x + y
}

fn add_u16(x: u16, y: u16) -> u16 {
    x + y
}

fn add_u128(x: u128, y: u128) -> u128 {
    x + y
}

fn sub_i8(x: i8, y: i8) -> i8 {
    x - y
}

fn sub_i16(x: i16, y: i16) -> i16 {
    x - y
}

fn sub_i128(x: i128, y: i128) -> i128 {
    x - y
}

fn main() {
    assert!(add_u8(1, 2) == 3);
    assert!(add_u16(1, 2) == 3);
    assert!(add_u128(1, 2) == 4);
    assert!(sub_i8(1, 2) == -1);
    assert!(sub_i16(1, 2) == -1);
    assert!(sub_i128(1, 2) == -1);
}

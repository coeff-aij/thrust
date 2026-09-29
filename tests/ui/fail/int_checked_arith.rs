//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

#[thrust_macros::requires(x <= u64::MAX)]
fn incr(x: u64) -> u64 {
    match x.checked_add(1) {
        Some(y) => y,
        None => panic!(),
    }
}

#[thrust_macros::requires(x > i64::MAX / 2)]
fn double_overflows(x: i64) {
    assert!(x.checked_mul(2).is_none());
}

fn main() {
    match 200u8.checked_add(56) {
        Some(_) => assert!(false),
        None => {}
    }
    match (-100i8).checked_sub(28) {
        Some(d) => assert!(d == -128),
        None => assert!(false),
    }
    match (-100i8).checked_sub(29) {
        Some(_) => assert!(false),
        None => {}
    }
    match (-8i8).checked_mul(16) {
        Some(p) => assert!(p == -128),
        None => assert!(false),
    }
    match 16u8.checked_mul(16) {
        Some(_) => assert!(false),
        None => {}
    }
    match 2u32.checked_sub(3) {
        Some(_) => assert!(false),
        None => {}
    }
}

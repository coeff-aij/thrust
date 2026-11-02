//@check-pass
//@compile-flags: -C debug-assertions=off

#[thrust_macros::requires(x >= 0 && y >= x)]
#[thrust_macros::ensures(result >= 0)]
fn diff(x: i64, y: i64) -> i64 {
    thrust_macros::proof_assert!(|x: i64, y: i64| y - x >= 0);
    y - x
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(!p == 3)]
fn set(p: &mut i64) {
    *p = 3;
    thrust_macros::proof_assert!(|p: &mut i64| *p == 3);
}

fn main() {
    let mut a = 0;
    set(&mut a);
    assert!(diff(1, a) >= 0);
}

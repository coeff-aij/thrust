//@check-pass
//@compile-flags: -C debug-assertions=off

const BIG: u128 = 1u128 << 100;

#[thrust_macros::requires(x < 1267650600228229401496703205376u128)]
#[thrust_macros::ensures(result == x + 1267650600228229401496703205376u128)]
fn add_big(x: u128) -> u128 {
    x + BIG
}

#[thrust_macros::requires(x < 18446744073709551615usize)]
#[thrust_macros::ensures(result == x + 1)]
fn succ(x: usize) -> usize {
    x + 1
}

fn is_max(x: usize) -> bool {
    match x {
        usize::MAX => true,
        _ => false,
    }
}

fn main() {
    assert!(add_big(1) == BIG + 1);
    assert!(is_max(succ(usize::MAX - 1)));
    assert!(!is_max(usize::MAX - 1));
}

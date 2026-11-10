//@check-pass
//@compile-flags: -C debug-assertions=off

// `#[thrust::assumed_ensures]` assumes the postcondition at the returns, as an `assume!` of it
// before each would: a false one, as both of these are, verifies, and callers rely on it. Thrust
// warns at it, and `THRUST_REPORT=functions` lists it.
#[thrust::assumed_ensures]
#[thrust_macros::requires(x >= 0 && x < 100)]
#[thrust_macros::ensures(result == x + 2)]
fn add_two(x: i64) -> i64 {
    x + 1
}

#[thrust::assumed_ensures]
#[thrust_macros::requires(*x >= 0 && *x < 100)]
#[thrust_macros::ensures(!x == *x + 2)]
fn bump_two(x: &mut i64) {
    *x += 1;
}

fn main() {
    let y = add_two(1);
    assert!(y == 3);
    let mut z = 1;
    bump_two(&mut z);
    assert!(z == 3);
}

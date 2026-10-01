//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables

// Trusted contracts with unsigned results: the return value and the final value of the `&mut u32`
// are taken as the contracts state them, and the values are non-negative as their type says.
#[thrust::trusted]
#[thrust_macros::requires(n >= 1)]
#[thrust_macros::ensures(result == n - 1)]
fn pred(n: u32) -> u32 {
    n - 1
}

#[thrust::trusted]
#[thrust_macros::requires(*x >= 1)]
#[thrust_macros::ensures(!x == *x - 1)]
fn dec(x: &mut u32) {
    *x -= 1;
}

fn main() {
    let y = pred(1);
    assert!(y == 0);
    let mut a: u32 = 3;
    dec(&mut a);
    assert!(a == 2);
}

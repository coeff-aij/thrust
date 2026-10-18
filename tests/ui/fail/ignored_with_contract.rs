//@compile-flags: -C debug-assertions=off

// An ignored function is invisible to Thrust, so a contract on it would be one nothing checks or
// states as trusted; it is rejected in favour of `#[thrust::trusted]`.

#[thrust::ignored]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == 1)]
fn f() -> i32 { //~ ERROR: `#[thrust::ignored]` cannot have a contract
    1
}

fn main() {
    assert!(f() == 1);
}

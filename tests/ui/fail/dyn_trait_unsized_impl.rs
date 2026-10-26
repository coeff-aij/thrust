//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The impl for `str` returns 0, which the trait's contract, applied to it although its
// companions carry `Self: Sized`, does not allow.

#[thrust_macros::context]
trait Tr {
    #[thrust_macros::ensures(result >= 3)]
    fn m(&self) -> u32;
}

impl Tr for str {
    fn m(&self) -> u32 {
        0
    }
}

fn g<T: Tr + ?Sized>(x: &T) -> u32 {
    x.m()
}

fn main() {
    let r = g("abc");
    assert!(r >= 3);
}

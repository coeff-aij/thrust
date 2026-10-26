//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The trait-contract companions carry `Self: Sized`, and the contract still applies to an impl
// for an unsized type: `g` at `T = str` relies on it, and the impl is checked against it.

#[thrust_macros::context]
trait Tr {
    #[thrust_macros::ensures(result >= 3)]
    fn m(&self) -> u32;
}

impl Tr for str {
    fn m(&self) -> u32 {
        3
    }
}

fn g<T: Tr + ?Sized>(x: &T) -> u32 {
    x.m()
}

fn main() {
    let r = g("abc");
    assert!(r >= 3);
}

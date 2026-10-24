//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables -A dead_code
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The impl of `Tr<bool>` concludes `p`, derived at `Tr<isize>` for the same type. Accepted, as
// `client_requires`.

#[thrust_macros::context]
trait Tr<X> {
    #[thrust_macros::predicate(derived)]
    fn p(self, x: X) -> bool;

    #[thrust_macros::ensures(Self::p(*self, x))]
    fn step(&self, x: X);
}

#[derive(PartialEq, Clone, Copy)]
struct S {
    a: isize,
}

impl thrust_models::Model for S {
    type Ty = S;
}

#[thrust_macros::context]
impl Tr<isize> for S {
    fn step(&self, x: isize) {}
}

#[thrust_macros::context]
impl Tr<bool> for S {
    fn step(&self, x: bool) {
        need(*self, 42);
    }
}

#[thrust_macros::requires(<S as Tr<isize>>::p(s, x))]
fn need(s: S, x: isize) {}

fn main() {}

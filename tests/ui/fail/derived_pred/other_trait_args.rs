//@compile-flags: -C debug-assertions=off -A unused-variables -A dead_code
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// Rejected. `p` is derived at the impl of `Tr<isize>` for `S`; the impl of `Tr<bool>` for the same
// type is not one of its rule sites.

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
        need(*self, 42); //~ ERROR: the derived predicate
    }
}

#[thrust_macros::requires(<S as Tr<isize>>::p(s, x))]
fn need(s: S, x: isize) {}

fn main() {}

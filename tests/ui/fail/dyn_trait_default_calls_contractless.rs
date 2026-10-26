//@error-in-other-file: this cannot be checked of the impls it stands for
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A call of `h` through `dyn Tr` takes the contract of its default body, analyzed over `Self`
// assuming that `g`, which has no contract on the trait, accepts any arguments. At `Self = dyn Tr`
// that assumption would have to hold of every impl, which is not checked, so it is rejected.

#[thrust_macros::context]
trait Tr {
    fn g(&self) -> u32 {
        5
    }

    #[thrust_macros::ensures(result >= 1)]
    fn h(&self) -> u32 {
        self.g()
    }
}

struct C;

impl thrust_models::Model for C {
    type Ty = ();
}

impl Tr for C {}

fn main() {
    let c = C;
    let d: &dyn Tr = &c;
    assert!(d.h() >= 1);
}

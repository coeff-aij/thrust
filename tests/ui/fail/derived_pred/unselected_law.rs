//@compile-flags: -C debug-assertions=off -A unused-variables -A dead_code
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_VERIFY_ONLY=main,stay,S::step

// Rejected. With the inherited law `r_refl` outside `THRUST_VERIFY_ONLY` it is not checked for `S`,
// so it gives `r` no rule; without the selection the file is accepted.

#[thrust_macros::context]
trait Rel {
    #[thrust_macros::predicate(derived)]
    fn r(self, o: Self) -> bool;

    #[thrust_macros::law]
    #[thrust_macros::ensures(Self::r(*a, *a))]
    fn r_refl(a: &Self) {} //~ ERROR: assumed without being checked against a body

    #[thrust_macros::ensures(Self::r(*self, !self))]
    fn step(&mut self);
}

#[derive(PartialEq, Clone, Copy)]
struct S {
    a: isize,
}

impl thrust_models::Model for S {
    type Ty = S;
}

#[thrust_macros::context]
impl Rel for S {
    fn step(&mut self) {
        self.a += 1;
    }
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(I::r(*it, *it))]
fn stay<I: Rel>(it: &I) {}

fn main() {
    let s = S { a: 0 };
    stay(&s);
    assert!(false);
}

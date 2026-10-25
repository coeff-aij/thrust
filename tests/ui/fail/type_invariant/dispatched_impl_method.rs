//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `g` calls `take` at `T`; at `S` that runs `S::take` at `U := C`, which calls `C::bump` on a `C`
// that breaks the invariant. The impl method is analyzed at that instance.
#[thrust_macros::context]
trait Counter {
    #[thrust_macros::ensures(result <= 100)]
    fn bump(&mut self) -> u32;
}
struct C {
    n: u32,
}
impl thrust_models::Model for C {
    type Ty = Self;
}
#[thrust_macros::context]
impl Invariant for C {
    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        self.n % 2 == 0
    }
}
impl Counter for C {
    fn bump(&mut self) -> u32 {
        if self.n % 2 == 1 { 1000 } else { 0 }
    }
}
struct W<U>(U);
impl<U: thrust_models::Model> thrust_models::Model for W<U> {
    type Ty = U::Ty;
}
struct S;
impl thrust_models::Model for S {
    type Ty = ();
}
#[thrust_macros::context]
trait Tr {
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(result <= 100)]
    fn take<U: Counter>(&self, w: W<U>) -> u32;
}
impl Tr for S {
    fn take<U: Counter>(&self, mut w: W<U>) -> u32 {
        w.0.bump()
    }
}
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result <= 100)]
fn g<T: Tr>(t: &T) -> u32 {
    t.take(W(C { n: 1 }))
}
fn main() {
    let r = g(&S);
    assert!(r <= 100);
}

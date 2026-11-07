//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
//@rustc-env: THRUST_VERIFY_ONLY=caller,h,W::m,other

// `W`'s `m`, selected with `other`, is `FnMut`-bounded through its impl's parameter and verified at each concrete
// closure (D34); `other`'s closure is such an instance. The selected generic `h` reaches `m` only
// through `Tr`, and `caller` runs `h` at `W` holding a closure that returns 2 at 1: that dispatched
// instance is analyzed when `h`'s instance is checked.

#[thrust_macros::context]
trait Tr {
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(true)]
    fn m(&mut self) -> i32;
}
struct W<F>(F);
impl<F> thrust_models::Model for W<F> {
    type Ty = thrust_models::model::Closure<F>;
}
impl<F: FnMut(i32) -> i32> Tr for W<F> {
    fn m(&mut self) -> i32 {
        let r = (self.0)(1);
        assert!(r != 0);
        r
    }
}
#[thrust::callable]
fn h<T: Tr>(mut t: T) -> i32 {
    t.m()
}
#[thrust::callable]
fn caller() {
    let k = 1;
    h(W(|x: i32| {
        let _k = k;
        x + 1
    }));
}
#[thrust::callable]
fn other() {
    let mut n = 0;
    W(|x: i32| { n += 1; x + 1 }).m();
}
fn main() {}

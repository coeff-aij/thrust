//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
//@rustc-env: THRUST_VERIFY_ONLY=make THRUST_PER_INSTANCE_GENERICS=1

// `make` returns a closure that `caller`, outside the selection, puts behind `&dyn Get`, whose per-
// instance `S::get` runs it. No analysis in `make`'s run checks that instance, so the closure
// leaving verified code must carry a written contract, as it does here.

#[thrust_macros::context]
trait Get {
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(true)]
    fn get(&self) -> i32;
}
struct S<F>(F);
impl<F> thrust_models::Model for S<F> {
    type Ty = thrust_models::model::Closure<F>;
}
#[thrust_macros::context]
impl<F: Fn() -> i32> Get for S<F> {
    fn get(&self) -> i32 {
        let r = (self.0)();
        assert!(r != 0);
        r
    }
}
#[thrust::callable]
fn make() -> impl Fn() -> i32 + Copy {
    thrust_macros::closure!(requires(true), ensures(result == 1), || -> i32 { 1 })
}
#[thrust::callable]
fn caller() {
    let s = S(make());
    let d: &dyn Get = &s;
    let _ = d.get();
}
fn main() {}

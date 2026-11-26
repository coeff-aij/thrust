//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
//@rustc-env: THRUST_VERIFY_ONLY=caller,h

// `W`'s `m`, outside the selection, is `FnMut`-bounded through its impl's parameter and analyzed at
// the instances this run's code runs. The selected generic `h`, whose contract `caller` uses, runs
// it only through `Tr`, at the instance `caller` makes: `h`'s body at that instance resolves the
// call to `m` at `W` holding a closure whose contract says it returns 0 at 1
// (`verify_only/generic_fn_mut_dispatched_selected.rs` selects `m`).

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
    h(W(thrust_macros::closure!(
        requires(true),
        ensures(result == x - 1),
        |x: i32| -> i32 {
            let _k = k;
            x - 1
        },
    )));
}

#[thrust::callable]
fn other() {
    let mut n = 0;
    W(|x: i32| { n += 1; x + 1 }).m();
}
fn main() {}

//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `W`'s `apply` is `FnMut`-bounded through its impl's parameter and verified at each concrete
// closure (D34); `conc`'s closure is such an instance. `gen` reaches `apply` only through `Ap`,
// and `caller2` runs it at `W` holding `dec`: that dispatched instance is analyzed, where `dec`'s
// assertion holds at 1.
#[thrust_macros::context]
trait Ap {
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(true)]
    fn apply(&mut self) -> i32;
}

struct W<F> {
    f: F,
}

impl<F> thrust_models::Model for W<F> {
    type Ty = W<thrust_models::model::Closure<F>>;
}

impl<F: FnMut(i32) -> i32> Ap for W<F> {
    fn apply(&mut self) -> i32 {
        (self.f)(1)
    }
}

#[thrust::callable]
fn gen<T: Ap>(t: &mut T) -> i32 {
    t.apply()
}

fn dec(x: i32) -> i32 {
    assert!(x > 0);
    x + 1
}

#[thrust::callable]
fn caller2() {
    let mut w = W { f: dec };
    gen(&mut w);
}

#[thrust::callable]
fn conc() {
    let mut n = 0;
    let mut w = W {
        f: |x| {
            n += 1;
            x + 1
        },
    };
    w.apply();
}

fn main() {}

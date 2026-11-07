//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `Ap`'s default `apply`, which `S` keeps, is `FnMut`-bounded and verified at each concrete
// closure (D34). `conc`'s closure is such an instance; `gen3` reaches `apply` only through `Ap` at
// `T`, and the trusted `caller` runs `gen3` at `S`, an instance analyzed nowhere but through the
// default's analysis over `F`, which is therefore emitted: there the assertion fails, as an
// arbitrary closure may return 0 at 1.

#[thrust_macros::context]
trait Ap {
    #[thrust_macros::requires(thrust_macros::pre!(f(1)))]
    #[thrust_macros::ensures(true)]
    fn apply<F: FnMut(i32) -> i32>(&self, mut f: F) -> i32 {
        let r = f(1);
        assert!(r != 0);
        r
    }
}

#[derive(PartialEq)]
struct S;

impl thrust_models::Model for S {
    type Ty = S;
}

impl Ap for S {}

#[thrust::callable]
fn gen3<T: Ap>(t: &T) -> i32 {
    t.apply(|x| x - 1)
}

#[thrust::trusted]
#[thrust::callable]
fn caller() {
    gen3(&S);
}

#[thrust::callable]
fn conc() {
    let mut n = 0;
    S.apply(|x| {
        n += 1;
        x + 1
    });
}

fn main() {}

//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `S::apply` and `gen` are `FnMut`-bounded and verified per instance (D34). `gen` reaches `apply`
// at its own type parameter `G`; `conc` instantiates `gen` with a closure that returns 0 at 1,
// where `apply`'s assertion fails.

#[thrust_macros::context]
trait Ap {
    #[thrust_macros::requires(thrust_macros::pre!(f(1)))]
    #[thrust_macros::ensures(true)]
    fn apply<F: FnMut(i32) -> i32>(&self, f: F) -> i32;
}

#[derive(PartialEq)]
struct S;

impl thrust_models::Model for S {
    type Ty = S;
}

impl Ap for S {
    fn apply<F: FnMut(i32) -> i32>(&self, mut f: F) -> i32 {
        let r = f(1);
        assert!(r != 0);
        r
    }
}

#[thrust_macros::requires(thrust_macros::pre!(g(1)))]
#[thrust_macros::ensures(true)]
fn gen<G: FnMut(i32) -> i32>(s: &S, g: G) -> i32 {
    s.apply(g)
}

#[thrust::callable]
fn conc() {
    let mut n = 0;
    S.apply(|x| {
        n += 1;
        x + 1
    });
    gen(&S, |x| x - 1);
}

fn main() {}

//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `S::apply` is `FnMut`-bounded and verified at each concrete closure (D34). `conc`'s closure is
// such an instance; `gen` reaches `apply` at its own type parameter `G`, an instance analyzed
// nowhere but through `apply`'s analysis over `F`, which is therefore emitted: it fails
// for a closure returning 0.

#[thrust_macros::context]
trait Ap {
    #[thrust_macros::requires(true)]
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

#[thrust::callable]
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
}

fn main() {}

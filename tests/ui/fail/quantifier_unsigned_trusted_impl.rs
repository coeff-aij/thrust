//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A trait method's contract that a trusted impl implements is read over Rust values for every impl
// and caller: a caller through a type parameter may reach the trusted body.
use thrust_models::forall;

#[thrust_macros::context]
trait Least {
    #[thrust_macros::ensures(forall(|n: u64| result <= n))]
    fn least(&self) -> u64;
}

struct A;

impl thrust_models::Model for A {
    type Ty = ();
}

#[thrust_macros::context]
impl Least for A {
    #[thrust::trusted]
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(forall(|n: u64| result <= n))]
    fn least(&self) -> u64 {
        0
    }
}

fn via<T: Least>(t: &T) -> u64 {
    t.least()
}

fn main() {
    let r = via(&A);
    assert!(r == 1);
}

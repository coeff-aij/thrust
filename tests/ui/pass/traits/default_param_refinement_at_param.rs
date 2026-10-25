//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `sides` writes only a parameter refinement, so its contract is not written in full: a call at
// `T` takes the unspecified type, which accepts any argument, and the method that runs at an
// instance must accept any argument there. `Sq`'s override does; the default, which requires
// `k > 0`, does not (`fail/traits/default_param_refinement_at_param.rs`).
#[thrust_macros::context]
trait Shape: thrust_models::Model {
    #[thrust_macros::param(k: { v: u32 | v > 0 })]
    fn sides(&self, k: u32) -> u32 {
        assert!(k > 0);
        3
    }
}

struct Sq;

impl thrust_models::Model for Sq {
    type Ty = ();
}

impl Shape for Sq {
    fn sides(&self, k: u32) -> u32 {
        2
    }
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn f<T: Shape>(s: &T) -> u32 {
    s.sides(0)
}

fn main() {
    f(&Sq);
}

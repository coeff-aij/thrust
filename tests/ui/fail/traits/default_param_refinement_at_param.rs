//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `sides` writes only a parameter refinement, so its contract is not written in full: a call at
// `T` takes the unspecified type, which accepts any argument. The default runs at `Sq` and requires
// `k > 0`, which the call at `T` did not establish.
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

impl Shape for Sq {}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn f<T: Shape>(s: &T) -> u32 {
    s.sides(0)
}

fn main() {
    f(&Sq);
}

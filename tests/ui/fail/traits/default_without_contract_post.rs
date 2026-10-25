//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `post!` of `sides` at `T` names the predicate every impl's result satisfies, not the type of the
// default body, which `Sq` overrides.
trait Shape {
    fn sides(&self) -> u32 {
        3
    }
}

struct Sq;

impl thrust_models::Model for Sq {
    type Ty = ();
}

impl Shape for Sq {
    fn sides(&self) -> u32 {
        2
    }
}

#[thrust_macros::ensures(thrust_macros::post!(<T as Shape>::sides(s), result))]
fn f<T: Shape>(s: &T) -> u32 {
    3
}

fn main() {
    let r = f(&Sq);
    assert!(r == 2);
}

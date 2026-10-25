//@error-in-other-file: instantiates a type parameter with the trait object
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A type parameter instantiated with a trait object is rejected: the callee's contract and the
// laws of its bounds would be assumed of `dyn Shape`.

#[thrust_macros::context]
trait Shape {
    #[thrust_macros::ensures(result >= 3)]
    fn sides(&self) -> u32;
}

struct Tri;

impl thrust_models::Model for Tri {
    type Ty = ();
}

impl Shape for Tri {
    fn sides(&self) -> u32 {
        3
    }
}

#[thrust_macros::ensures(result >= 3)]
fn g<T: ?Sized + Shape>(s: &T) -> u32 {
    s.sides()
}

fn main() {
    let t = Tri;
    let s: &dyn Shape = &t;
    assert!(g::<dyn Shape>(s) >= 3);
}

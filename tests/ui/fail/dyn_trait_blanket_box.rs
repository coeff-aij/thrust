//@error-in-other-file: instantiates a type parameter with the trait object
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// An impl for `Box<T>` at `T: ?Sized` used at `T = dyn Shape` instantiates its type parameter
// with a trait object, which is rejected as `g::<dyn Shape>` is.

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

impl<T: ?Sized + Shape> Shape for Box<T> {
    fn sides(&self) -> u32 {
        (**self).sides()
    }
}

fn main() {
    let b: Box<dyn Shape> = Box::new(Tri);
    assert!(b.sides() >= 3);
}

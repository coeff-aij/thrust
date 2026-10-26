//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A function generic over `T: ?Sized + Shape` used at a sized type.

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
    assert!(g::<Tri>(&t) >= 3);
}

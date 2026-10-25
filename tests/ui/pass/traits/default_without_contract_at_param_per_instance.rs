//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
//@rustc-env: THRUST_PER_INSTANCE_GENERICS=1

// `sides` has no contract, so a call at `T` takes no type from the default body, which `Sq`
// overrides: it accepts any argument and says nothing of the result.
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

#[thrust_macros::ensures(true)]
fn f<T: Shape>(s: &T) -> u32 {
    s.sides()
}

fn main() {
    f(&Sq);
}

//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The default `sides` calls `raw` at `Self`, where a contractless `raw` takes no type from its
// default body, which `Sq` overrides.
#[thrust_macros::context]
trait Shape {
    fn raw(&self) -> u32 {
        3
    }

    #[thrust_macros::ensures(result >= 3)]
    fn sides(&self) -> u32 {
        self.raw()
    }
}

struct Sq;

impl thrust_models::Model for Sq {
    type Ty = ();
}

impl Shape for Sq {
    fn raw(&self) -> u32 {
        4
    }
}

fn main() {
    let s = Sq;
    assert!(s.sides() >= 3);
}

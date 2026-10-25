//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_PER_INSTANCE_GENERICS=1

// `fail/traits/default_without_contract_at_param.rs` with each generic body analyzed at its
// instances: the call at `Sq` takes `Sq`'s override, not the default's type.
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

#[thrust_macros::ensures(result >= 3)]
fn f<T: Shape>(s: &T) -> u32 {
    s.sides()
}

fn main() {
    let r = f(&Sq);
    assert!(r >= 3);
}

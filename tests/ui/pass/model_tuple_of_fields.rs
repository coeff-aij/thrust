//@check-pass
//@compile-flags: -C debug-assertions=off

// A `Model` that is a tuple with a component per field has the shape of the struct, and the
// fields are read from its components.
use thrust_models::model::Int;

struct P {
    a: i64,
    b: i64,
}

impl thrust_models::Model for P {
    type Ty = (Int, Int);
}

#[thrust_macros::context]
#[thrust_macros::ensures(result == 3)]
fn sum() -> i64 {
    let p = P { a: 1, b: 2 };
    p.a + p.b
}

fn main() {
    assert!(sum() == 3);
}

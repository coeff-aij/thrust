//@compile-flags: -C debug-assertions=off

// A `Model` whose `Ty` has fewer components than the struct has fields has nothing to project
// a field from, so Thrust stops at the impl.
struct S {
    a: i64,
    b: i64,
}

impl thrust_models::Model for S { //~ ERROR: has not its shape
    type Ty = (thrust_models::model::Int,);
}

fn main() {
    let _ = S { a: 1, b: 2 };
}

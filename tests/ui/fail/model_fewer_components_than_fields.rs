//@error-in-other-file: with fewer components than its fields
//@compile-flags: -C debug-assertions=off

// A `Model` whose `Ty` has fewer components than the struct has fields has nothing to project
// a field from, so Thrust stops where the struct is compared.
#[derive(PartialEq)]
struct S {
    a: i64,
    b: i64,
}

impl thrust_models::Model for S {
    type Ty = (thrust_models::model::Int,);
}

fn main() {
    let x = S { a: 1, b: 2 };
    let y = S { a: 1, b: 3 };
    assert!(x == y);
}

//@compile-flags: -C debug-assertions=off

// `type Ty = ()` for a struct with a field leaves the field without a component to read.
struct S {
    a: i64,
}

impl thrust_models::Model for S { //~ ERROR: has not its shape
    type Ty = ();
}

fn main() {
    let _ = S { a: 1 };
}

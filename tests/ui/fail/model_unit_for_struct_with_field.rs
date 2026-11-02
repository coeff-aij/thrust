//@error-in-other-file: of another shape than its fields
//@compile-flags: -C debug-assertions=off

// `type Ty = ()` for a struct with a field leaves the constructed value without a component per
// field, so Thrust stops where the struct is built.
struct S {
    a: i64,
}

impl thrust_models::Model for S {
    type Ty = ();
}

fn take(_s: S) {}

fn main() {
    take(S { a: 1 });
}

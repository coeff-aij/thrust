//@error-in-other-file: is `#[thrust::ignored]`
//@compile-flags: -C debug-assertions=off

// An ignored impl method's body is not checked against the trait's spec in `std.rs`, so a call
// that resolves to it cannot take that spec: `==` runs the panicking `eq`.

struct S(i32);

impl thrust_models::Model for S {
    type Ty = Self;
}

impl PartialEq for S {
    #[thrust::ignored]
    fn eq(&self, _o: &S) -> bool {
        assert!(false);
        true
    }
}

fn main() {
    let a = S(1);
    let _ = a == a;
}

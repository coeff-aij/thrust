//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off

struct Inner {
    c: i64,
}

impl thrust_models::Model for Inner {
    type Ty = Self;
}

struct Outer {
    b: Inner,
}

impl thrust_models::Model for Outer {
    type Ty = Self;
}

#[thrust_macros::requires(a.b.c == 42)]
#[thrust_macros::ensures(true)]
fn test(a: Outer) {
    assert!(a.b.c == 42);
}

fn main() {
    test(Outer { b: Inner { c: 42 } });
}

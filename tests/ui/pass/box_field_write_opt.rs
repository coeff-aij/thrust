//@check-pass
//@compile-flags: -C debug-assertions=off -C opt-level=1
//@rustc-env: THRUST_OPTIMIZED_MIR=1

// At `-C opt-level=1` the `deref_copy` of the `Box` behind `b` becomes a `copy`, through which
// the field is written.
struct Tri {
    a: u32,
}

impl thrust_models::Model for Tri {
    type Ty = Self;
}

fn set(b: &mut Box<Tri>) {
    b.a = 5;
}

fn main() {
    let mut b = Box::new(Tri { a: 1 });
    set(&mut b);
    assert!(b.a == 5);
}

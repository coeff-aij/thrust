//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:develop-2493045c3

// A derived Clone and PartialEq compare a Vec field through std.rs's generic
// trait-side specs (`_extern_spec_clone`, `_extern_spec_partialeq_eq`), which
// apply to any Self type structurally, not through a spec on Vec's own impl.

#[derive(Clone, PartialEq)]
struct Pair {
    items: Vec<i32>,
    tag: i32,
}

impl thrust_models::Model for Pair {
    type Ty = Pair;
}

fn main() {
    let mut items = Vec::new();
    Vec::push(&mut items, 4);
    let p = Pair { items, tag: 9 };
    let q = p.clone();
    assert!(q == p);
}

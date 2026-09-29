//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:develop-2493045c3

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
    let mut q = p.clone();
    q.tag += 1;
    assert!(q == p);
}

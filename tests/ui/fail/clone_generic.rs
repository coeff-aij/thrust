//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

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
    assert!(q.tag == 9);
    assert!(q.items.len() == 1);
    assert!(q.items[0] == 5);
}

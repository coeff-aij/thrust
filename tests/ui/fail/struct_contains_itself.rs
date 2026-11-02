//@compile-flags: -Adead_code -C debug-assertions=off

// A struct is modelled by the tuple of its fields, which a struct reaching itself does not have.

struct Node { //~ ERROR: the struct `Node` contains itself through its fields
    v: i64,
    next: Option<Box<Node>>,
}

fn get(n: &Node) -> i64 {
    n.v
}

fn main() {}

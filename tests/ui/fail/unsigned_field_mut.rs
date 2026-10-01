//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

struct Counter {
    n: usize,
}

// Writing a value that may be negative through `&mut` breaks the field's invariant.
fn drop_one(c: &mut Counter) {
    c.n -= 1;
}

fn main() {
    let mut c = Counter { n: 0 };
    drop_one(&mut c);
}

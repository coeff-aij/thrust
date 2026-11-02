//@check-pass
//@compile-flags: -C debug-assertions=off

// An immutable `static` without interior mutability keeps its initializer's value, read directly
// and through a constant that refers to it.

static N: i64 = 7;
static P: (i64, bool) = (3, true);
const R: &i64 = &N;

fn get() -> i64 {
    N
}

fn main() {
    assert!(get() == 7);
    assert!(P.0 == 3 && P.1);
    assert!(*R == 7);
}

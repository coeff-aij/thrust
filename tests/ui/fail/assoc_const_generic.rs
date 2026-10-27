//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

trait Sides {
    const N: u32;
}

struct Tri;

impl Sides for Tri {
    const N: u32 = 3;
}

// Checked over `S`, at which `S::N` is any `u32`, and again at `Tri`.
fn sides<S: Sides>() -> u32 {
    S::N
}

fn main() {
    assert!(sides::<Tri>() == 4);
}

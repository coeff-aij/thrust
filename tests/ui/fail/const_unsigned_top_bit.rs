//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

fn id(x: u32) -> u32 {
    x
}

fn main() {
    assert!(id(4294967295) < 0);
    assert!(id(4294967295) == 4294967295);
}

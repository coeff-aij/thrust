//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// A pointer to a function without a specification may be made; calling it must be unreachable.
fn main() {
    let f: fn() -> u32 = std::process::id;
    let _ = f();
}

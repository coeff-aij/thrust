//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// A function without a specification that does not return (`std::process::exit`) must be
// unreachable too.
fn f(x: i64) -> i64 {
    if x < 0 {
        std::process::exit(1);
    }
    x
}

fn main() {
    let _ = f(-1);
}

//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A string literal in a value of the program has the null sort of `str`.
#[derive(Clone, Copy)]
enum E {
    A(&'static str),
    B,
}

fn f(e: E) -> u32 {
    match e {
        E::A(_) => 1,
        E::B => 2,
    }
}

fn main() {
    let x = f(E::A("x"));
    assert!(x == 2);
}

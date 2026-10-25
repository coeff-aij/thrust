//@error-in-other-file: trait objects are supported only of the crate's own traits
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `dyn Fn` is rejected: trait objects are supported only of the crate's own traits.

fn call(f: &dyn Fn() -> u32) -> u32 {
    f()
}

fn main() {
    let r = call(&|| 3);
    assert!(r == 3);
}

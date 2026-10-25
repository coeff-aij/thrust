//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A closure called through a reference at a type parameter bounded by `Fn`.

fn call<F: Fn() -> u32>(f: &F) -> u32 {
    f()
}

fn main() {
    let r = call(&|| 3);
    assert!(r == 3);
}

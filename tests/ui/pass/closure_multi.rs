//@check-pass
//@compile-flags: -C debug-assertions=off

fn call<F: Fn() -> i32>(f: F) -> i32 {
    f()
}

fn main() {
    let mut f = || 1;
    let mut g = || -1;

    assert!(call(f) > 0);
    assert!(call(g) < 0);
}
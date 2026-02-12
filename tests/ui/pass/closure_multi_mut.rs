//@check-pass
//@compile-flags: -C debug-assertions=off

fn call<F: FnMut() -> i32>(f: &mut F) -> i32 {
    f()
}

fn main() {
    let mut i = 0;
    let mut j = 0;
    let mut f = || {i += 1; i};
    let mut g = || {j -= 1; j};

    assert!(call(&mut f) > 0);
    assert!(call(&mut g) < 0);
    assert!(call(&mut f) > 1);
}
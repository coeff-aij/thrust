//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// A closure in generic code that captures a function pointer, called by std code (Option::map)
// through its pre!/post!.
fn inc(x: i64) -> i64 {
    x + 1
}

fn run<T>(_t: T) -> Option<i64> {
    let g: fn(i64) -> i64 = inc;
    let c = move |v: i64| -> i64 { g(v) };
    Some(1i64).map(c)
}

fn main() {
    let r = run(0u8);
    assert!(r == Some(2));
}

//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// An FnOnce closure (it moves out a captured unit struct) that captures a function pointer,
// called by std code (Option::map) through its pre!/post!.
fn inc(x: i64) -> i64 {
    x + 1
}

struct Tok;

fn main() {
    let g: fn(i64) -> i64 = inc;
    let t = Tok;
    let c = move |v: i64| -> i64 {
        let _t = t;
        g(v)
    };
    let r = Some(1i64).map(c);
    assert!(r == Some(2));
}

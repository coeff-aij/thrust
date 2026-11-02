//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-spacer-wrapper

// The call of an `FnMut` closure through `Option::map` drops its final state, which resolves the
// `&mut` it holds in the payload of an `Option`: `n` is what the closure wrote.
fn main() {
    let mut n: i64 = 0;
    let mut o = Some(&mut n);
    let c = move |v: i64| -> i64 {
        if let Some(x) = &mut o {
            **x += v;
        }
        0
    };
    let _r = Some(5i64).map(c);
    assert!(n == 5);
}

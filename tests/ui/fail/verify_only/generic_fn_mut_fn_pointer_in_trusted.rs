//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
//@rustc-env: THRUST_VERIFY_ONLY=caller

// The FnMut-bounded `g` is checked at each closure it runs with. The trusted generic `tg` turns
// `g::<F>` into a function pointer and calls it, at the closure the selected `caller` passes, which
// returns 0 at its call: no call reaches that instance directly, and the walk over what `caller`
// runs finds it through `tg`'s body at `caller`'s closure. `helper` makes another instance, so no
// run analyzes `g` over `F`.

#[thrust::callable]
fn g<F: FnMut() -> i32>(mut f: F) -> i32 {
    let r = f();
    assert!(r != 0);
    r
}
fn helper() -> i32 {
    g(|| 1)
}
#[thrust::trusted]
#[thrust::callable]
fn tg<F: FnMut() -> i32 + 'static>(f: F) -> i32 {
    let h: fn(F) -> i32 = g::<F>;
    h(f)
}
#[thrust::callable]
fn caller<T: Copy + 'static>(x: T) {
    let _ = helper();
    let c = move || {
        let _ = x;
        0
    };
    let _ = tg(c);
}
fn main() {}

//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
//@rustc-env: THRUST_VERIFY_ONLY=caller

// The shape of `generic_fn_mut_fn_pointer_in_trusted.rs` with `tg` holding `g::<F>` in a promoted
// constant (`&[g::<F>]`), which `mentioned_items` does not list: the walk reads the promoted body
// at `tg`'s instance.

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
    let fs: &'static [fn(F) -> i32] = &[g::<F>];
    (fs[0])(f)
}
#[thrust::callable]
fn caller<T: Copy + 'static>(x: T) {
    let _ = helper();
    let c = move || {
        let _ = x;
        1
    };
    let _ = tg(c);
}
fn main() {}

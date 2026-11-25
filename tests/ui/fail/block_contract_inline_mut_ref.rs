//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
fn main() {
    let mut a = 0i64;
    let r = &mut a;
    thrust_macros::block_contract_inline!(
        |r: &mut i64| -> ()
        requires(*r == 0),
        ensures(!r == 1),
        {
            *r += 1;
        }
    );
    *r += 2;
    assert!(a == 2);
}

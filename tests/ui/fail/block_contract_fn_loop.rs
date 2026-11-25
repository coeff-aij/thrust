//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
fn main() {
    let mut i = 0i64;
    let k = 7i64;
    thrust_macros::block_contract_fn!(
        |i: &mut i64| -> ()
        requires(*i == 0),
        ensures(!i == 9),
        {
            while *i < 10 {
                *i += 1;
            }
        }
    );
    assert!(i == 10 && k == 7);
}

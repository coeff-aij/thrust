//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// wrong twin of `pass/block_contract_mut_ref_read_only.rs`: the kept value is asserted to be another
fn main() {
    let mut a = 3i64;
    let r = &mut a;
    let v = thrust_macros::block_contract!(
        |r: &mut i64| -> i64
        requires(true),
        ensures(result == *r),
        {
            *r
        }
    );
    assert!(*r == 4 && v == 3);
}

//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
fn main() {
    let mut x = 5i64;
    let y = thrust_macros::block_contract_inline!(
        |mut x: i64| -> i64
        requires(x == 5),
        ensures(old!(x) == 5 && x == 6 && result == 7),
        {
            x += 1;
            x + 1
        }
    );
    assert!(y == x);
}

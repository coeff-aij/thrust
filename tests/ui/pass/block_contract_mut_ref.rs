//@check-pass
//@compile-flags: -C debug-assertions=off

// A `&mut` the code under the contract writes through keeps its final value, so the write
// reaches the borrowed variable when the reference ends after the code.
fn main() {
    let mut a = 0i64;
    let r = &mut a;
    thrust_macros::block_contract!(
        requires(|r: &mut i64| *r == 0),
        ensures(|r: &mut i64| *r == 1),
        {
            *r += 1;
        }
    );
    *r += 1;
    assert!(a == 2);
}

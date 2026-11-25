//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
// The block is verified from `requires` alone, which is checked where the block is written.
#[thrust::trusted]
#[thrust::callable]
fn rand() -> i64 {
    unimplemented!()
}
fn main() {
    let n = rand();
    let mut x = if n > 0 { n } else { 0 };
    thrust_macros::block_contract!(
        |mut x: i64| -> ()
        requires(x > 0),
        ensures(x > 1),
        {
            x = x * 2;
        }
    );
    assert!(x > 1);
}

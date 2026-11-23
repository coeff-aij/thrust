//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// The code under the contract starts from `requires` alone, which is checked where it is
// written.
#[thrust::trusted]
#[thrust::callable]
fn rand() -> i64 {
    unimplemented!()
}

fn main() {
    let n = rand();
    let mut x = if n > 0 { n } else { 0 };
    thrust_macros::block_contract!(
        requires(|x: i64| x > 0),
        ensures(|x: i64| x > 1),
        {
            x = x * 2;
        }
    );
    assert!(x > 1);
}

//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -C panic=abort
// Two blocks one after the other: the second, reached only past the first, uses `i` after two
// calls, and its `requires` names it.
#[thrust::trusted]
#[thrust::callable]
fn rand() -> i64 {
    unimplemented!()
}
fn id(x: i64) -> i64 {
    x
}
fn main() {
    let mut x = 0i64;
    let i = if rand() > 0 { 1i64 } else { 0i64 };
    let mut w = 0i64;
    thrust_macros::block_contract!(
        |mut x: i64| -> ()
        requires(x == 0),
        ensures(x == 1),
        {
            x = id(x + 1);
        }
    );
    thrust_macros::block_contract!(
        |x: i64, mut w: i64, i: i64| -> ()
        requires(x == 1 && 0 <= i && i <= 1),
        ensures(w == i + 1),
        {
            let y = id(x);
            let z = id(y) + 1;
            w = z + i;
        }
    );
    assert!(w == i + 1);
}

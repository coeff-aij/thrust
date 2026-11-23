//@check-pass
//@compile-flags: -C debug-assertions=off -C panic=abort

// Two contracts one after the other: the code under the second, reached only past the first,
// uses `i` after two calls, and its `requires` names it. With `panic=abort` no cleanup
// block leads back into the code, so its liveness comes from its own successors alone.
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
        requires(|x: i64| x == 0),
        ensures(|x: i64| x == 1),
        {
            x = id(x + 1);
        }
    );
    thrust_macros::block_contract!(
        requires(|x: i64, i: i64| x == 1 && 0 <= i && i <= 1),
        ensures(|w: i64, i: i64| w == i + 1),
        {
            let y = id(x);
            let z = id(y);
            w = z + i;
        }
    );
    assert!(w == i + 1);
}

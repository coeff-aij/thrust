//@compile-flags: -C debug-assertions=off

// A `return` out of the braces leaves the code under the contract before its end.
#[thrust::trusted]
#[thrust::callable]
fn rand() -> i64 {
    unimplemented!()
}

fn f(x: i64) -> i64 {
    let y = thrust_macros::block_contract!( //~ ERROR: a path from `block_requires!` leaves the function before a `block_ensures!`
        requires(|x: i64| x == x),
        ensures(|result: i64, x: i64| result == x),
        {
            if x < 0 {
                return 0;
            }
            x
        }
    );
    y
}

fn main() {
    let _ = f(rand());
}

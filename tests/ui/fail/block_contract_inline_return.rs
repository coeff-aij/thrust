//@compile-flags: -C debug-assertions=off

// A `return` out of the block leaves the code under the contract before its end.
#[thrust::trusted]
#[thrust::callable]
fn rand() -> i64 {
    unimplemented!()
}

fn f(x: i64) -> i64 {
    let y = thrust_macros::block_contract_inline!( //~ ERROR: a path from `block_contract_inline!` leaves the function before a `block_contract_inline!` end marker
        |x: i64| -> i64
        ensures(result == x),
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

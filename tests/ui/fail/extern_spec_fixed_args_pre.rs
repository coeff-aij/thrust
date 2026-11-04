//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `pre!` names the contract of a function at the instance an extern spec covers: at fixed type
// arguments (`cmp::max::<u64>`) and at some fixed and some free (`Option::<i32>::zip::<u8>`).

#[thrust::extern_spec_fn]
#[thrust_macros::requires(v1 != 5)]
#[thrust_macros::ensures(result == v1 || result == v2)]
fn _extern_spec_max_word(v1: u64, v2: u64) -> u64 {
    std::cmp::max(v1, v2)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(a != None)]
#[thrust_macros::ensures(true)]
fn _extern_spec_zip_byte<T: thrust_models::Model>(
    a: Option<T>,
    b: Option<u8>,
) -> Option<(T, u8)> {
    Option::zip(a, b)
}

#[thrust_macros::requires(thrust_macros::pre!(std::cmp::max::<u64>(a, b)))]
#[thrust_macros::ensures(true)]
fn call_max(a: u64, b: u64) -> u64 {
    std::cmp::max(a, b)
}

#[thrust_macros::requires(thrust_macros::pre!(Option::<i32>::zip::<u8>(a, b)))]
#[thrust_macros::ensures(true)]
fn call_zip(a: Option<i32>, b: Option<u8>) -> Option<(i32, u8)> {
    a.zip(b)
}

fn main() {
    let _ = call_max(5, 4);
    let _ = call_zip(Some(1), None);
}

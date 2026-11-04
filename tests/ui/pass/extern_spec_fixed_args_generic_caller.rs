//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// An extern spec of `Option::unwrap_or` at `u64` does not cover the call in `or_default` at its
// type parameter, which takes std.rs's generic spec.

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result >= 0)]
fn _extern_spec_option_unwrap_or_word(opt: Option<u64>, default: u64) -> u64 {
    Option::unwrap_or(opt, default)
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(opt != None || result == default)]
fn or_default<T: thrust_models::Model>(opt: Option<T>, default: T) -> T {
    opt.unwrap_or(default)
}

fn main() {
    let x = or_default(None, 3u64);
    assert!(x == 3);
}

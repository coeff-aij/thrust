//@check-pass
//@compile-flags: -C debug-assertions=off

// An extern spec of `Option::unwrap_or` at `u64` says nothing of a call at `i64`, whose type has
// the same sort: that call takes std.rs's generic spec.

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result >= 0)]
fn _extern_spec_option_unwrap_or_word(opt: Option<u64>, default: u64) -> u64 {
    Option::unwrap_or(opt, default)
}

fn main() {
    let x = Some(-1i64).unwrap_or(0);
    assert!(x == -1);
}

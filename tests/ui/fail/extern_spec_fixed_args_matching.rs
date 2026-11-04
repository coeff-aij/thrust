//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// An extern spec of `Option::unwrap_or` at `u64` is the contract of the calls at `u64`, in place
// of std.rs's generic spec: its precondition is checked there.

#[thrust::extern_spec_fn]
#[thrust_macros::requires(default > 0)]
#[thrust_macros::ensures(
    (opt != None && Some(result) == opt)
    || (opt == None && result == default)
)]
fn _extern_spec_option_unwrap_or_word(opt: Option<u64>, default: u64) -> u64 {
    Option::unwrap_or(opt, default)
}

fn main() {
    let x = Some(3u64).unwrap_or(0);
    assert!(x == 3);
}

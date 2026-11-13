//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -A unused-variables -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The twin of `pass/uint_enum_payload_facts.rs`: the payload is not above `0`.
#[thrust_macros::requires(matches!(o, Some(_)))]
#[thrust_macros::ensures(match o { Some(x) => x > 0, None => true })]
fn payload(o: Option<usize>) {}

fn main() {}

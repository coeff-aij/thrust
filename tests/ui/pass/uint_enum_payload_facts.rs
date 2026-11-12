//@check-pass
//@compile-flags: -Adead_code -A unused-variables -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The payload of an enum value at an unsigned type is `>= 0` in every mode.

#[thrust_macros::requires(matches!(o, Some(_)))]
#[thrust_macros::ensures(match o { Some(x) => x >= 0, None => true })]
fn payload(o: Option<usize>) {}

fn main() {}

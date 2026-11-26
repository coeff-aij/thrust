//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A variable a quantifier binds ranges over its type's values at every depth of its enum
// payloads, also without `THRUST_INT_RANGE`: the `char` under nine `Option`s is a Unicode scalar
// value.
use thrust_models::forall;

type O9 = Option<Option<Option<Option<Option<Option<Option<Option<Option<char>>>>>>>>>;

#[thrust_macros::ensures(forall(|o0: O9| match o0 { Some(o1) => match o1 { Some(o2) => match o2 { Some(o3) => match o3 { Some(o4) => match o4 { Some(o5) => match o5 { Some(o6) => match o6 { Some(o7) => match o7 { Some(o8) => match o8 { Some(c) => c <= char::MAX, None => true }, None => true }, None => true }, None => true }, None => true }, None => true }, None => true }, None => true }, None => true }))]
fn nested_char_in_range() {}

fn main() {}

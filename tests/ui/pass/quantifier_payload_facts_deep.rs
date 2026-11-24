//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A variable a quantifier binds ranges over the values of its type at every depth of its enum
// payloads: the `u8` under nine enums is non-negative.
use thrust_models::forall;

enum E0 { W(E1), Z }
enum E1 { W(E2), Z }
enum E2 { W(E3), Z }
enum E3 { W(E4), Z }
enum E4 { W(E5), Z }
enum E5 { W(E6), Z }
enum E6 { W(E7), Z }
enum E7 { W(E8), Z }
enum E8 { V(u8), Z }

#[thrust_macros::ensures(forall(|e: E0| match e { E0::W(e1) => match e1 { E1::W(e2) => match e2 { E2::W(e3) => match e3 { E3::W(e4) => match e4 { E4::W(e5) => match e5 { E5::W(e6) => match e6 { E6::W(e7) => match e7 { E7::W(e8) => match e8 { E8::V(x) => x >= 0, _other => true }, _other => true }, _other => true }, _other => true }, _other => true }, _other => true }, _other => true }, _other => true }, _other => true }))]
fn deep_payload_non_negative() {}

fn main() {}

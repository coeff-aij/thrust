//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A variable a quantifier binds at a sequence of enums holding a `char` ranges over the sequences
// whose elements' payloads are Unicode scalar values, as every value of its type is, so that
// statement holds of it. (The `assume!` form of `quantifier_char_range.rs` over this type is not
// decided by PCSat in 120 s.)
use thrust_models::forall;
use thrust_models::model::{Int, Seq};

#[thrust_macros::ensures(forall(|s: Seq<Option<char>>| forall(|i: Int| (0 <= i && i < s.len())
    ==> match s[i] {
        Some(c) => c <= char::MAX,
        None => true,
    })))]
fn payloads_in_range() {}

fn main() {}

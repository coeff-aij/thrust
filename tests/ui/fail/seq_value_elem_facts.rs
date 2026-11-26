//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The elements of a sequence value have the facts of their type in every mode: those of a
// `Vec<Option<u64>>` are `>= 0` in their payloads, as a variable a quantifier binds at that type is.
use thrust_models::forall;

#[thrust_macros::ensures(forall(|i: thrust_models::model::Int|
    (0 <= i && i < (*v).len()) ==> match (*v)[i] { Some(n) => n >= 1, None => true }))]
fn payloads_nonneg(v: &Vec<Option<u64>>) {}

fn main() {}

//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A lemma marked `#[thrust_macros::law]` outside a trait is assumed wherever a function its
// contract applies is used, also at values the program does not name: here at every pair of
// sequences and prefix that `everywhere`'s postcondition ranges over. (The solver proves this
// postcondition without the law as well; the law matters for facts it cannot prove by itself.)

use thrust_models::Ghost;
use thrust_models::model::{Int, Seq, UInt};
use thrust_models::forall;

// The `true` entries among the first `k` of `acc`.
#[thrust_macros::logic]
#[thrust_macros::variant(k)]
fn trues(acc: Seq<bool>, k: usize) -> Int {
    if k <= 0 {
        0
    } else {
        trues(acc, k - 1) + if acc[k - 1] { 1 } else { 0 }
    }
}

// A concatenation's first `k <= a.len()` entries are `a`'s.
#[thrust_macros::lemma]
#[thrust_macros::law]
#[thrust_macros::variant(k)]
#[thrust_macros::requires(k <= a.len())]
#[thrust_macros::ensures(trues(a.concat(b), k) == trues(a, k))]
fn trues_concat_prefix(a: Ghost<Seq<bool>>, b: Ghost<Seq<bool>>, k: usize) {
    if k > 0 {
        trues_concat_prefix(a, b, k - 1);
    }
}

// The law at every pair of sequences and every prefix, with no call.
#[thrust_macros::lemma]
#[thrust_macros::ensures(forall(|a: Seq<bool>| forall(|b: Seq<bool>| forall(|k: UInt|
    !(k <= a.len()) || trues(a.concat(b), k) == trues(a, k)))))]
fn everywhere() {}

fn main() {}

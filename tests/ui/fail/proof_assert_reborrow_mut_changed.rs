//@compile-flags: -C debug-assertions=off
// A `&mut` copied from `*mm` cannot be named after `*mm` may have changed: the borrow checker
// ends `k`'s borrow at its last use, so `old`, the same reference, writes the integer.
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn g<'a, 'b>(mm: &'b mut &'a mut i64, other: &'a mut i64) {
    let k: &mut i64 = mm;
    *k = 6;
    let old: &mut i64 = std::mem::replace(mm, other);
    *old = 7;
    thrust_macros::proof_assert!(|k: &mut i64, old: &mut i64| *k != *old); //~ ERROR: a formula refers to `k`, a `&mut` copied from a place that may change between the copy and here
}

fn main() {}

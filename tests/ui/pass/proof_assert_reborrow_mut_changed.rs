//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `k` is a reborrow of `**mm`, so the model keeps it as a borrow of its own, and a formula that
// names `k` reads its value at its last use (6), as Creusot does, even though `*mm` is replaced
// and the old referent is written through `old` afterwards.
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn g<'a, 'b>(mm: &'b mut &'a mut i64, other: &'a mut i64) {
    let k: &mut i64 = mm;
    *k = 6;
    let old: &mut i64 = std::mem::replace(mm, other);
    *old = 7;
    thrust_macros::proof_assert!(|k: &mut i64, old: &mut i64| *k == 6 && *old == 7);
}

fn main() {}

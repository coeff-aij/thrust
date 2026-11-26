//@check-pass
//@compile-flags: -C debug-assertions=off -C panic=abort
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120

// A `for` loop with no written invariant in the body of a block contract is desugared as in the
// function around it, with the structural invariant where the iterator implements
// `IteratorSpec`; `no_structural_invariant!()` opts a loop of the body out.

#[thrust_macros::context]
fn with_facts() -> i64 {
    let mut c = 0i64;
    thrust_macros::block_contract!(
        |mut c: i64| -> ()
        requires(c == 0),
        ensures(c == 3),
        {
            for _i in 0..3i64 {
                c += 1;
            }
        }
    );
    c
}

#[thrust_macros::context]
fn without_facts() -> i64 {
    let mut c = 0i64;
    thrust_macros::block_contract!(
        |mut c: i64| -> ()
        requires(c == 0),
        ensures(c == 2),
        {
            for _i in 0..2i64 {
                thrust_macros::no_structural_invariant!();
                c += 1;
            }
        }
    );
    c
}

fn main() {
    assert!(with_facts() == 3);
    assert!(without_facts() == 2);
}

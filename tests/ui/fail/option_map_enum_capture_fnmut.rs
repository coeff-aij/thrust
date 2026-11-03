//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-spacer-wrapper

// A let-bound closure that moves in an `Option<&mut i64>` and writes through it is `FnMut`.
// `Option::map` requires its precondition, which includes the refinement of the payload of the
// `Option` it captures, and its call ends the borrow at the value it left. (PCSat does not answer
// the failing twin within the timeout.)
fn main() {
    let mut n: i64 = 0;
    let mut o = Some(&mut n);
    let c = move |v: i64| -> i64 {
        if let Some(x) = &mut o {
            **x += v;
        }
        0
    };
    let r = Some(5i64).map(c);
    assert!(r == Some(1));
}

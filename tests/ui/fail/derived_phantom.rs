//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The derived impls of a generic struct with a `PhantomData` field are not analyzed: `clone` and
// `eq` have std.rs's contracts over the model, and `Hash` and `Debug` are present but unused.

use std::marker::PhantomData;

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
struct IdxRange<I> {
    start: usize,
    end: usize,
    marker: PhantomData<fn(&I)>,
}

fn main() {
    let r: IdxRange<u32> = IdxRange { start: 0, end: 3, marker: PhantomData };
    let s = r.clone();
    assert!(s.end == 3);
    assert!(r != s);
}

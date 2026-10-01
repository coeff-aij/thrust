//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables -A unused_mut

// Soundness check for unsigned facts: under the guard, `x - 1` is -1 in the logic (it wraps at run
// time, so the `assert!` fails). The value reaches a position whose type says it is non-negative
// through a loop-carried local. If that position assumed the fact without an obligation, the
// contradiction would verify the `assert!` vacuously; the expected error is the obligation where
// the value enters the position.
#[thrust::callable]
fn f(x: usize, k: usize) {
    if x == 0 && k == 1 {
        let mut i: usize = x;
        let mut j = 0;
        while j < k {
            i = i - 1;
            j += 1;
        }
        assert!(i == 7);
    }
}

fn main() {}

//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables -A unused_mut

// Soundness check for unsigned facts: under the guard, `x - 1` is -1 in the logic (it wraps at run
// time, so the `assert!` fails). The value reaches a position whose type says it is non-negative
// through a shared reference to the value. If that position assumed the fact without an
// obligation, the contradiction would verify the `assert!` vacuously; the expected error is the
// obligation where the value enters the position.
fn read(r: &usize) -> usize {
    *r
}

#[thrust::callable]
fn f(x: usize) {
    if x == 0 {
        let a = x - 1;
        let r = read(&a);
        assert!(r == 7);
    }
}

fn main() {}

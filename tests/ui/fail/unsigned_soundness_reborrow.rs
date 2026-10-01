//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables -A unused_mut

// Soundness check for unsigned facts: under the guard, `x - 1` is -1 in the logic (it wraps at run
// time, so the `assert!` fails). The value reaches a position whose type says it is non-negative
// through a reborrow passed on to the writer. If that position assumed the fact without an
// obligation, the contradiction would verify the `assert!` vacuously; the expected error is the
// obligation where the value enters the position.
fn set(r: &mut usize, x: usize) {
    *r = x - 1;
}

fn pass_on(r: &mut usize, x: usize) {
    set(&mut *r, x);
}

#[thrust::callable]
fn f(x: usize) {
    if x == 0 {
        let mut a: usize = 0;
        pass_on(&mut a, x);
        assert!(a == 7);
    }
}

fn main() {}

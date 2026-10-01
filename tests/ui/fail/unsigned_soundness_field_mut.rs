//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables -A unused_mut

// Soundness check for unsigned facts: under the guard, `x - 1` is -1 in the logic (it wraps at run
// time, so the `assert!` fails). The value reaches a position whose type says it is non-negative
// through a field write behind `&mut`. If that position assumed the fact without an obligation,
// the contradiction would verify the `assert!` vacuously; the expected error is the obligation
// where the value enters the position.
struct C {
    n: usize,
}

fn set(c: &mut C, x: usize) {
    c.n = x - 1;
}

#[thrust::callable]
fn f(x: usize) {
    if x == 0 {
        let mut c = C { n: 0 };
        set(&mut c, x);
        assert!(c.n == 7);
    }
}

fn main() {}

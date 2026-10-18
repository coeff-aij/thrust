//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// `t.0` is moved out of `t` on one path only, so where the paths join it may be moved, and
// dropping `t` must not resolve it there: `a` is 5 at the assertion when `c` holds.

fn cond() -> bool {
    true
}

fn main() {
    let mut a = 0;
    let t = (Some(&mut a), 1);
    let c = cond();
    if c {
        let y = t.0;
        if let Some(r) = y {
            *r = 5;
        }
    }
    assert!(a == 0);
}

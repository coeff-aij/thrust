//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// `q` is the temporary of `deref_copy (*s).0`, read after `set` receives `copy s` and
// overwrites `(*s).0`.

#[inline(never)]
fn set<'a>(s: &mut (&'a i32, i32), b: &'a i32) {
    s.0 = b;
}

#[inline(never)]
fn f<'a>(s: &mut (&'a i32, i32), b: &'a i32) -> i32 {
    let q: &i32 = &*s.0;
    set(s, b);
    s.1 += 1;
    *q
}

fn main() {
    let a = 1;
    let b = 2;
    let mut p = (&a, 0);
    let r = f(&mut p, &b);
    assert!(r == 2);
}

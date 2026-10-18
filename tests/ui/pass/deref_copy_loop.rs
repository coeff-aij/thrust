//@check-pass
//@compile-flags: -C debug-assertions=off

// `q` is the temporary of `deref_copy s.0`, read after a later iteration overwrites `s.0`.

fn inc(x: &mut i32) {
    *x += 1;
}

fn main() {
    let mut a = 0;
    let mut b = 0;
    let mut ob = Some(&mut b);
    let mut s = (&mut a, 0);
    let q = &mut *s.0;
    let mut i = 0;
    while i < 2 {
        s.1 += 1;
        inc(q);
        if i == 0 {
            s.0 = ob.take().unwrap();
        }
        i += 1;
    }
    assert!(b == 0);
}

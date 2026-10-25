//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// Constants read from their allocation: arrays, tuples, enums and references inside them.
const R: &[u32; 3] = &[1, 2, 3];
const T: &[(u8, bool); 2] = &[(1, true), (2, false)];
const N: &[i8; 2] = &[-1, -128];
const O: &[Option<u8>; 2] = &[None, Some(5)];
const P: &(u16, &u32) = &(7, &9);

fn main() {
    let r: &[u32] = R;
    match r.last() {
        Some(x) => assert!(*x == 3),
        None => assert!(false),
    }
    let t: &[(u8, bool)] = T;
    match t.last() {
        Some(x) => assert!(!x.1 && x.0 == 2),
        None => assert!(false),
    }
    let n: &[i8] = N;
    match n.last() {
        Some(x) => assert!(*x == -128),
        None => assert!(false),
    }
    let o: &[Option<u8>] = O;
    match o.last() {
        Some(x) => assert!(*x == Some(5)),
        None => assert!(false),
    }
    assert!(*P.1 == 7 && P.0 == 7);
}

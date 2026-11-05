//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

fn inc(x: i64) -> i64 {
    x + 1
}

fn chk(x: i64) -> i64 {
    assert!(x != 1);
    x
}

fn set(r: &mut fn(i64) -> i64) {
    *r = chk;
}

fn main() {
    let mut g: fn(i64) -> i64 = inc;
    set(&mut g);
    g(1);
}

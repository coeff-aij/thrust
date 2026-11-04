//@error-in-other-file: Unsat
//@compile-flags: -C overflow-checks=on -C debug-assertions=off

// In a specification, `p.0` of a `&mut (i64, i64)` is a field of the current value, `(*p).0`.
#[thrust_macros::requires(0 <= p.0 && p.0 < 100)]
#[thrust_macros::ensures((!p).0 == p.0 + 2 && (!p).1 == p.1)]
fn inc(p: &mut (i64, i64)) {
    p.0 += 1;
}

fn main() {}

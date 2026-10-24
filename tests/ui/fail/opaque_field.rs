//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off

// A raw pointer and a trait object are opaque: a type may hold them (`fmt::Arguments` does),
// and verified code passes them on without observing them.
struct Handle<'a> {
    ptr: Option<*const u8>,
    sink: &'a dyn std::fmt::Debug,
    n: i32,
}

fn get_n(h: Handle) -> i32 {
    h.n
}

#[thrust::callable]
fn check(h: Handle) {
    let n = h.n;
    assert!(get_n(h) == n + 1);
}

fn main() {}

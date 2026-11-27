//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
// A closure with a capture that std code (Option::unwrap_or_else) calls, and that panics.
fn overflow(_a: u32) -> u32 {
    panic!()
}
fn add(a: u32, b: u32) -> u32 {
    let s = (a as u64) + (b as u64);
    if s > 100 {
        return 0;
    }
    let o: Option<u32> = if s > 50 { None } else { Some(s as u32) };
    o.unwrap_or_else(|| overflow(a))
}
fn main() {
    let r = add(30, 40);
    assert!(r == 70);
}

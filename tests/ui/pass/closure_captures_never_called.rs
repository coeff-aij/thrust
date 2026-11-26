//@check-pass
//@compile-flags: -C debug-assertions=off
// A closure with a capture that std code (Option::unwrap_or_else) never calls: its precondition,
// which states its captures, may be false although the closure is built.
fn overflow(_a: u32) -> u32 {
    panic!()
}
fn add(a: u32, b: u32) -> u32 {
    let s = (a as u64) + (b as u64);
    if s > 100 {
        return 0;
    }
    let o: Option<u32> = Some(s as u32);
    o.unwrap_or_else(|| overflow(a))
}
fn main() {
    let r = add(1, 2);
    assert!(r == 3);
}

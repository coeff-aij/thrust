//@error-in-other-file: would promise the invariant
//@compile-flags: -Adead_code -C debug-assertions=off -Aunused

// std's `Option::<i64>::is_some`, whose extern spec in std.rs is generic over `T`, returns a
// `bool`, whose invariant std never keeps.
#[thrust_macros::context]
impl Invariant for bool {
    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        self
    }
}
fn main() {
    let o: Option<i64> = None;
    let b = o.is_some();
    assert!(b);
}

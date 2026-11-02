//@compile-flags: -Adead_code -C debug-assertions=off -Aunused

// `Invariant` is implemented only for a type of the crate: std's `Option::<i64>::is_some` returns
// a `bool`, whose invariant std never keeps.
#[thrust_macros::context]
impl Invariant for bool { //~ ERROR: `Invariant` can be implemented only for a type defined in this crate
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

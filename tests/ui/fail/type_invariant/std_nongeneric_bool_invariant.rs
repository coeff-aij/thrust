//@compile-flags: -Adead_code -C debug-assertions=off -Aunused

// As `std_generic_bool_invariant.rs` with the non-generic `i32::is_positive`.
#[thrust_macros::context]
impl Invariant for bool { //~ ERROR: `Invariant` can be implemented only for a type defined in this crate
    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        self
    }
}
fn main() {
    let x: i32 = -1;
    let b = x.is_positive();
    assert!(b);
}

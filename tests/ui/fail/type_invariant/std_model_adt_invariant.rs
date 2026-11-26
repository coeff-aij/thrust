//@compile-flags: -Adead_code -C debug-assertions=off -Aunused
use thrust_models::model::Int;
// A type of the injected `std.rs` is not defined in the crate either.
#[thrust_macros::context]
impl Invariant for Int { //~ ERROR: `Invariant` can be implemented only for a type defined in this crate
    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        true
    }
}
fn main() {}

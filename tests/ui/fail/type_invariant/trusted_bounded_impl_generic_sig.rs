//@error-in-other-file: would promise the invariant
//@compile-flags: -Adead_code -C debug-assertions=off -Aunused

// As `pass/type_invariant/trusted_bounded_impl.rs`, with the type parameter in the signature,
// behind a reference: the contract was written over `T`, so it cannot promise `Even`'s invariant.
struct Even(i64);
impl thrust_models::Model for Even {
    type Ty = Self;
}
#[thrust_macros::context]
impl Invariant for Even {
    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        self.0 % 2 == 0
    }
}
trait K {}
struct Z;
impl K for Z {}
struct W<T>(T);
#[thrust_macros::context]
impl<T: K> W<T> {
    #[thrust::trusted]
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(result.0 >= 0)]
    fn mk(_t: &T) -> Even {
        Even(0)
    }
}
fn main() {
    let e = W::<Z>::mk(&Z);
    assert!(e.0 % 2 == 0);
}

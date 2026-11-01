//@error-in-other-file: would promise the invariant
//@compile-flags: -Adead_code -C debug-assertions=off -Aunused

// As `pass/type_invariant/trusted_bounded_impl.rs`, with the result of the trusted method of the
// type parameter itself: its contract was written over `T`, so at `T = Even` it cannot promise
// `Even`'s invariant.
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
impl K for Even {}
struct W<T>(T);
#[thrust_macros::context]
impl<T: K> W<T> {
    #[thrust::trusted]
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(true)]
    fn id(t: T) -> T {
        t
    }
}
fn main() {
    let e = W::<Even>::id(Even(0));
    assert!(e.0 % 2 == 0);
}

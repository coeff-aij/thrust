//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off -Aunused

// A trusted method of a bounded impl whose signature does not mention the impl's type
// parameter: its contract promises `Even`'s invariant at every instance, as it does outside the impl.
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
    fn mk() -> Even {
        Even(0)
    }
}
fn main() {
    let e = W::<Z>::mk();
    assert!(e.0 % 2 == 0);
}

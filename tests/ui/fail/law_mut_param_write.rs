//@compile-flags: -Adead_code -Aunused -C debug-assertions=false

// A law is assumed for every value of its parameters, both components of a `&mut` included,
// while its proof only has to hold for the final value its body leaves. A law that takes a
// `&mut` is rejected, as a lemma is.

use thrust_models::Model;

#[thrust_macros::context]
trait L: Model {
    #[thrust_macros::predicate]
    fn seven(self) -> bool;

    #[thrust_macros::law]
    #[thrust_macros::ensures(Self::seven(!a))]
    fn set(a: &mut Self); //~ ERROR: a law cannot take or return a `&mut`
}

#[derive(Clone, Copy)]
struct A(i64);

impl Model for A {
    type Ty = (thrust_models::model::Int,);
}

#[thrust_macros::context]
impl L for A {
    #[thrust_macros::predicate]
    fn seven(self) -> bool {
        self.0 == 7
    }

    fn set(a: &mut A) { //~ ERROR: a law cannot take or return a `&mut`
        a.0 = 7;
    }
}

#[thrust_macros::context]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(T::seven(*x))]
fn g<T: L>(x: &T) {}

fn main() {}

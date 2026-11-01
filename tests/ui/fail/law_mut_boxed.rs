//@compile-flags: -Adead_code -Aunused -C debug-assertions=false

// A `&mut` inside a `Box` is one a law could write through, though `Box` keeps its argument
// behind a raw pointer.

use thrust_models::Model;

#[thrust_macros::context]
trait L: Model {
    #[thrust_macros::predicate]
    fn p(self) -> bool;

    #[thrust_macros::law]
    #[thrust_macros::ensures(Self::p(!*b))]
    fn l(b: Box<&mut Self>); //~ ERROR: a law cannot take or return a `&mut`
}

fn main() {}

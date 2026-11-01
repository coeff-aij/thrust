//@compile-flags: -Adead_code -Aunused -C debug-assertions=false

// The proof of a law over a `&mut` need not write through it: an empty proof leaves the final
// value equal to the current one, and the law would still be assumed for every final value.

use thrust_models::Model;

#[thrust_macros::context]
trait L: Model {
    #[thrust_macros::predicate]
    fn same(self, o: Self) -> bool;

    #[thrust_macros::law]
    #[thrust_macros::ensures(Self::same(*a, !a))]
    fn keep(a: &mut Self); //~ ERROR: a law cannot take or return a `&mut`
}

#[derive(Clone, Copy)]
struct A(i64);

impl Model for A {
    type Ty = (thrust_models::model::Int,);
}

#[thrust_macros::context]
impl L for A {
    #[thrust_macros::predicate]
    fn same(self, o: A) -> bool {
        self.0 == o.0
    }

    fn keep(a: &mut A) {} //~ ERROR: a law cannot take or return a `&mut`
}

fn main() {}

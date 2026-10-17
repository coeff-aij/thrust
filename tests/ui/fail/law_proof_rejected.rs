//@compile-flags: -Adead_code -C debug-assertions=off

// What would let a law's proof fail to terminate: its contract is assumed wherever the trait is
// used through a type parameter, so a proof that does not return would prove anything.

use thrust_models::Model;

#[thrust_macros::context]
trait Pos
where
    Self: Model,
{
    #[thrust_macros::predicate]
    fn pos(self) -> bool;

    #[thrust_macros::law]
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(Self::pos(*a))]
    fn all_pos(a: &Self);

    #[thrust_macros::law]
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(Self::pos(*a))]
    fn all_pos_again(a: &Self);
}

#[derive(PartialEq)]
struct Spin(i64);

impl Model for Spin {
    type Ty = Spin;
}

#[thrust_macros::context]
impl Pos for Spin {
    #[thrust_macros::predicate]
    fn pos(self) -> bool {
        self.0 > 0
    }

    fn all_pos(a: &Spin) {
        loop {} //~ ERROR: a lemma or a law's proof cannot contain a loop
    }

    fn all_pos_again(a: &Spin) {
        Self::all_pos(a) //~ ERROR: a lemma or a law's proof calls only lemmas, logic functions, predicates, model operations and laws at a type parameter
    }
}

fn helper() {}

#[derive(PartialEq)]
struct Helped(i64);

impl Model for Helped {
    type Ty = Helped;
}

#[thrust_macros::context]
impl Pos for Helped {
    #[thrust_macros::predicate]
    fn pos(self) -> bool {
        self.0 > 0
    }

    fn all_pos(a: &Helped) {
        helper() //~ ERROR: a lemma or a law's proof calls only lemmas, logic functions, predicates, model operations and laws at a type parameter
    }

    fn all_pos_again(a: &Helped) {}
}

fn main() {}

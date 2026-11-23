//@compile-flags: -Adead_code -C debug-assertions=off

// A variable at a type whose definition holds itself at other type arguments through a projection
// (`Nest<Option<T>>` with a field `Option<T::A>`) is rejected: the search for a type without values
// would not end there.
use thrust_models::forall;

trait Tr {
    type A;
}

struct X;

impl Tr for X {
    type A = i64;
}

impl<T: Tr> Tr for Option<T> {
    type A = T::A;
}

enum Nest<T: Tr> {
    L(Option<T::A>),
    N(Box<Nest<Option<T>>>),
}

fn main() {
    let x = 0i64;
    thrust_macros::assume!(|x: i64| x == 0
        && forall(|n: Nest<X>| match n { Nest::L(_) => true, Nest::N(_) => true })); //~ ERROR: its definition holds itself at other type arguments through a projection
    assert!(x == 1);
}

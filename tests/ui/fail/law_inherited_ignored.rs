//@compile-flags: -C debug-assertions=off

// A law is assumed at every type parameter of its trait because each impl proves it. An impl
// that inherits a law Thrust cannot check there, here one whose default body is ignored, is
// rejected rather than left unchecked.
use thrust_models::Model;

#[thrust_macros::context]
trait Tr
where
    Self: Model,
{
    #[thrust_macros::predicate]
    fn p(self) -> bool;

    #[thrust_macros::law]
    #[thrust::ignored]
    fn l(a: &Self) {}
}

#[derive(PartialEq)]
struct S {
    x: i64,
}

impl Model for S {
    type Ty = S;
}

#[thrust_macros::context]
impl Tr for S { //~ ERROR: this impl inherits has no contract to check it against here
    #[thrust_macros::predicate]
    fn p(self) -> bool {
        self.x > 0
    }
}

fn main() {}

//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60 COAR_IMAGE=coar:latest

// A generic function whose spec calls the predicate of a generic impl on a type that
// still contains the type parameter (`<Bar<T> as Foo>::valid`). `Instance::try_resolve`
// resolves this to the impl item, so the impl's `define-fun` body is used, not a forall
// predicate; only a call on the type parameter itself (`T::valid`) needs the latter.
use thrust_models::Model;

#[thrust_macros::context]
trait Foo {
    #[thrust_macros::predicate]
    fn valid(self, x: i64) -> bool;
}

#[derive(PartialEq)]
struct Bar<T>(T);

impl<T> Model for Bar<T> {
    type Ty = Bar<T>;
}

#[thrust_macros::context]
impl<T> Foo for Bar<T>
where
    T: Foo + Model + PartialEq,
    <T as Model>::Ty: PartialEq,
{
    #[thrust_macros::predicate]
    fn valid(self, x: i64) -> bool {
        "(> x 0)"; true
    }
}

#[thrust_macros::requires(<Bar<T> as Foo>::valid(b, v))]
#[thrust_macros::ensures(<Bar<T> as Foo>::valid(result, v))]
fn keep<T>(b: Bar<T>, v: i64) -> Bar<T>
where
    T: Foo + Model + PartialEq,
    <T as Model>::Ty: PartialEq,
{
    b
}

fn main() {}

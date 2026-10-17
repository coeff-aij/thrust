//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `Tr::ok` at `(T, u8)` and at `(T, i32)` are two trait predicates, which the impls define
// differently, though both types have one sort. Named by the sort, they were one symbol, `f`
// verified, and a `panic!()` after the call in `main` verified too.

#[thrust_macros::context]
trait Tr {
    #[thrust_macros::predicate]
    fn ok(self) -> bool;
}

struct A;

impl thrust_models::Model for A {
    type Ty = A;
}

#[thrust_macros::context]
impl Tr for (A, u8) {
    #[thrust_macros::predicate]
    fn ok(self) -> bool {
        true
    }
}

#[thrust_macros::context]
impl Tr for (A, i32) {
    #[thrust_macros::predicate]
    fn ok(self) -> bool {
        false
    }
}

#[thrust_macros::requires(<(T, u8) as Tr>::ok((x, a)) && a == 1 && b == 1)]
#[thrust_macros::ensures(<(T, i32) as Tr>::ok((x, b)))]
fn f<T: thrust_models::Model>(x: T, a: u8, b: i32)
where
    (T, u8): Tr,
    (T, i32): Tr,
{
}

fn main() {
    f(A, 1, 1);
}

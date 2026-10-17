//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `Tr::ok` at `(T, u8)` and at `(T, i32)` are two trait predicates, which the impls define
// differently, though both types have one sort. Named by the sort, they were one symbol, `f`
// verified, and a `panic!()` after the call in `main` verified too. So are `Tr::ok` at `T` and at
// `<T as Model>::Ty`, which `C` and its model `D` define differently.

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

struct C(i64);
struct D(i64);

impl thrust_models::Model for C {
    type Ty = D;
}

impl thrust_models::Model for D {
    type Ty = D;
}

#[thrust_macros::context]
impl Tr for C {
    #[thrust_macros::predicate]
    fn ok(self) -> bool {
        true
    }
}

#[thrust_macros::context]
impl Tr for D {
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

#[thrust_macros::requires(T::ok(x))]
#[thrust_macros::ensures(<T::Ty as Tr>::ok(x))]
fn g<T: thrust_models::Model + Tr>(x: T)
where
    T::Ty: Tr + thrust_models::Model<Ty = T::Ty>,
{
}

fn main() {
    f(A, 1, 1);
    g(C(1));
}

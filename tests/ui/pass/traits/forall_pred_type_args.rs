//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The twin of `fail/traits/forall_pred_type_args.rs`: `ok` at `(T, u8)`, at `T` and at
// `(T, Ch<'+'>)` follow from themselves.

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

struct Ch<const X: char>;

impl<const X: char> thrust_models::Model for Ch<X> {
    type Ty = Ch<X>;
}

#[thrust_macros::context]
impl Tr for (A, Ch<'+'>) {
    #[thrust_macros::predicate]
    fn ok(self) -> bool {
        true
    }
}

#[thrust_macros::context]
impl Tr for (A, Ch<'-'>) {
    #[thrust_macros::predicate]
    fn ok(self) -> bool {
        false
    }
}

#[thrust_macros::requires(<(T, u8) as Tr>::ok((x, a)) && a == 1 && b == 1)]
#[thrust_macros::ensures(<(T, u8) as Tr>::ok((x, a)))]
fn f<T: thrust_models::Model>(x: T, a: u8, b: i32)
where
    (T, u8): Tr,
    (T, i32): Tr,
{
}

#[thrust_macros::requires(T::ok(x))]
#[thrust_macros::ensures(T::ok(x))]
fn g<T: thrust_models::Model + Tr>(x: T)
where
    T::Ty: Tr + thrust_models::Model<Ty = T::Ty>,
{
}

#[thrust_macros::requires(<(T, Ch<'+'>) as Tr>::ok((x, p)))]
#[thrust_macros::ensures(<(T, Ch<'+'>) as Tr>::ok((x, p)))]
fn h<T: thrust_models::Model>(x: T, p: Ch<'+'>, m: Ch<'-'>)
where
    (T, Ch<'+'>): Tr,
    (T, Ch<'-'>): Tr,
{
}

fn main() {
    f(A, 1, 1);
    g(C(1));
    h(A, Ch, Ch);
}

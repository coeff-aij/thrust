//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The twin of `fail/traits/forall_pred_type_args.rs`: `ok` at `(T, u8)` follows from itself.

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
#[thrust_macros::ensures(<(T, u8) as Tr>::ok((x, a)))]
fn f<T: thrust_models::Model>(x: T, a: u8, b: i32)
where
    (T, u8): Tr,
    (T, i32): Tr,
{
}

fn main() {
    f(A, 1, 1);
}

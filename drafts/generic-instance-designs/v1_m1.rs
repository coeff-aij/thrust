#[thrust_macros::context]
trait Tr { fn m(&self, x: i32) -> i32; }
#[derive(PartialEq)]
struct S;
impl thrust_models::Model for S { type Ty = S; }
#[thrust_macros::context]
impl Tr for S {
    #[thrust_macros::requires(x > 0)]
    #[thrust_macros::ensures(true)]
    fn m(&self, x: i32) -> i32 { assert!(x > 0); x }
}
#[thrust::callable]
fn g<T: Tr>(t: &T) -> i32 { t.m(1) }
#[thrust::callable]
fn caller() -> i32 { g(&S) }
fn main() {}

//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
extern crate thrust_macros;
use thrust_macros::{context, ensures, logic, requires};
use thrust_models::model::UInt;
use thrust_models::Model;

#[context]
trait Account {
    #[ensures(result == Self::balance_logic(*self))]
    fn balance(&self) -> u32;
    #[ensures(Self::balance_logic(!self) == Self::balance_logic(*self) + amount)]
    fn deposit(&mut self, amount: u32);
    #[requires(Self::balance_logic(*self) >= amount)]
    #[ensures(Self::balance_logic(!self) == Self::balance_logic(*self) - amount)]
    fn withdraw(&mut self, amount: u32);
    #[logic]
    fn balance_logic(self) -> UInt;
}

#[requires(A::balance_logic(*a) >= 10)]
#[ensures(A::balance_logic(!a) == A::balance_logic(*a))]
fn withdraw_deposit<A: Account>(a: &mut A)
where
    A: Model,
    <A as Model>::Ty: Model
{
    a.withdraw(20);
    a.deposit(10);
}

fn main() {}

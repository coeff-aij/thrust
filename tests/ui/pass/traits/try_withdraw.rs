//@check-pass
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

#[ensures(A::balance_logic(!a) + result == A::balance_logic(*a))]
fn try_withdraw<A: Account>(a: &mut A, amount: u32) -> u32
where
    A: Model,
    <A as Model>::Ty: Model
{
    if a.balance() < amount {
        return 0;
    }
    a.withdraw(amount);
    return amount;
}

fn main() {}

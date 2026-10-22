// A bank account: withdraw only when the balance covers the amount.
extern crate thrust_macros;
use thrust_macros::{context, ensures, logic, requires};
use thrust_models::model::UInt;
use thrust_models::Model;

#[context]
trait Account {
    // The balance, a function used only in specifications.
    #[logic]
    fn balance_logic(self) -> UInt;

    // Reads the balance.
    #[ensures(result == Self::balance_logic(*self))]
    fn balance(&self) -> u32;

    // Deposit: the balance grows by `amount`.
    #[ensures(Self::balance_logic(!self) == Self::balance_logic(*self) + amount)]
    fn deposit(&mut self, amount: u32);

    // Withdrawal: allowed only when the balance is at least `amount`.
    #[requires(Self::balance_logic(*self) >= amount)]
    #[ensures(Self::balance_logic(!self) == Self::balance_logic(*self) - amount)]
    fn withdraw(&mut self, amount: u32);
}

// The amount withdrawn (`result`) plus the balance after is the balance before.
#[ensures(A::balance_logic(!a) + result == A::balance_logic(*a))]
fn try_withdraw<A: Account>(a: &mut A, amount: u32) -> u32
where
    A: Model,
    <A as Model>::Ty: Model
{
    if a.balance() < amount { // not enough money
        return 0;             // withdraw nothing
    }
    a.withdraw(amount);
    return amount;
}

fn main() {}

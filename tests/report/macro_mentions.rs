// Parameters read only inside a formula macro, a closure shadowing, and a typed closure binder.
use thrust_models::forall;
#[thrust_macros::lemma]
#[thrust_macros::requires(thrust_macros::pre!(f(x)))]
#[thrust_macros::ensures(true)]
fn lem_pre<F: Fn(i64) -> i64>(f: F, x: i64) {}

#[thrust_macros::lemma]
#[thrust_macros::requires(forall(|n: i64| thrust_macros::pre!(f(n))))]
#[thrust_macros::ensures(thrust_macros::post!(f(x), y))]
fn lem_post<F: Fn(i64) -> i64>(f: F, x: i64, y: i64) {}

#[thrust_macros::lemma]
#[thrust_macros::requires(forall(|n: i64| n >= 0 ==> n + 0 == n))]
#[thrust_macros::ensures(true)]
fn lem_shadow(n: i64) {}

fn main() {}

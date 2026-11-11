use thrust_models::forall;
#[thrust_macros::context]
#[thrust_macros::requires(forall(|x: i32| thrust_macros::pre!(f(x))))]
#[thrust_macros::ensures(result == 2)]
fn apply<F: Fn(i32) -> i32>(f: F) -> i32 {
    f(1)
}

fn main() {
    let _ = apply(|x| x + 1);
}

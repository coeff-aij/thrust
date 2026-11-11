use thrust_models::forall;
use thrust_models::model::Closure;
#[thrust_macros::context]
#[thrust_macros::requires(forall(|c: Closure<F>, y: i32| thrust_macros::pre!(c(y))))]
#[thrust_macros::ensures(result == 3)]
fn apply_twice<F: FnMut(i32) -> i32>(mut f: F) -> i32 {
    let a = f(1);
    f(a)
}

fn main() {
    let mut n = 0;
    let _ = apply_twice(|x| {
        n += 1;
        x + 1
    });
}

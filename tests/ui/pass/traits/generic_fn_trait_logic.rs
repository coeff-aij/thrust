//@check-pass
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A generic function whose signature does not mention its type parameter, with a contract that
// names the parameter's logic function: at `via::<Lin>` the contract reads `Lin`'s `score`.
#[thrust_macros::context]
trait Score {
    #[thrust_macros::logic]
    fn score(x: i32) -> i32;
    #[thrust_macros::ensures(result == Self::score(x))]
    fn eval(x: i32) -> i32;
}
struct Lin;
impl thrust_models::Model for Lin { type Ty = (); }
#[thrust_macros::context]
impl Score for Lin {
    #[thrust_macros::logic]
    fn score(x: i32) -> i32 { x }
    fn eval(x: i32) -> i32 { x }
}
#[thrust_macros::ensures(result == T::score(x))]
fn via<T: Score>(x: i32) -> i32 { T::eval(x) }
fn main() {
    assert!(via::<Lin>(3) == 3);
}

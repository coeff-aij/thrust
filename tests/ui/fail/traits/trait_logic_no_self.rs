//@error-in-other-file: Unsat
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// As the pass twin, with `eval` returning `x + 1`: at the impl, `Self::score` is the impl's
// `x`, which `eval` does not meet.
#[thrust_macros::context]
trait Score {
    #[thrust_macros::logic]
    fn score(x: i32) -> i32;

    #[thrust_macros::ensures(result == Self::score(x))]
    fn eval(x: i32) -> i32;
}

struct Lin;
impl thrust_models::Model for Lin {
    type Ty = ();
}

#[thrust_macros::context]
impl Score for Lin {
    #[thrust_macros::logic]
    fn score(x: i32) -> i32 {
        x
    }

    fn eval(x: i32) -> i32 {
        x + 1
    }
}

fn main() {}

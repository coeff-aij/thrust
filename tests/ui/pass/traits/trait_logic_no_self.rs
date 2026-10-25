//@check-pass
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A trait logic function without a `self` parameter, named by the trait method's contract: at the
// impl, `Self::score` is the impl's own, so `eval` returning `x` meets `result == Self::score(x)`,
// and a caller at `Lin` learns `score`'s value.
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
        x
    }
}

fn main() {
    assert!(Lin::eval(3) == 3);
}

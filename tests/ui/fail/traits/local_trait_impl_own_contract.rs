//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The pass twin with an impl contract, and a body, returning -1, which the trait's contract
// does not allow; both calls still hold under the contract each of them uses.

#[thrust_macros::context]
trait Get {
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(result >= 0)]
    fn get(&self) -> i64;
}

struct One;

impl thrust_models::Model for One {
    type Ty = ();
}

#[thrust_macros::context]
impl Get for One {
    #[thrust_macros::ensures(result == -1)]
    fn get(&self) -> i64 {
        -1
    }
}

fn via<T: Get>(t: &T) -> i64 {
    t.get()
}

fn main() {
    assert!(One.get() == -1);
    assert!(via(&One) >= 0);
}

//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest

#[derive(PartialEq)]
struct P {
    v: i64,
}

impl thrust_models::Model for P {
    type Ty = Self;
}

#[thrust_macros::context]
trait Tr {
    #[thrust_macros::predicate]
    fn ok(self) -> bool;

    #[thrust_macros::requires(Self::ok(*self))]
    #[thrust_macros::ensures(true)]
    fn use_it(&self) -> i64;
}

#[thrust_macros::context]
impl Tr for P {
    #[thrust_macros::predicate]
    fn ok(self) -> bool {
        "(>= (tuple_proj<Int>.0 self_) 0)";
        true
    }

    fn use_it(&self) -> i64 {
        assert!(self.v >= 0);
        self.v
    }
}

fn main() {
    let p = P { v: -1 };
    let _ = p.use_it();
}

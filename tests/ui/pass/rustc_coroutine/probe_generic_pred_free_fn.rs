//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest

struct P {
    v: i64,
}

impl thrust_models::Model for P {
    type Ty = P;
}

#[thrust_macros::context]
trait Tr {
    #[thrust_macros::predicate]
    fn ok(self) -> bool;

    #[thrust_macros::requires(Self::ok(*self))]
    #[thrust_macros::ensures(true)]
    fn use_it(&mut self) -> i64;
}

#[thrust_macros::context]
impl Tr for P {
    #[thrust_macros::predicate]
    fn ok(self) -> bool {
        "(>= (tuple_proj<Int>.0 self_) 0)";
        true
    }

    fn use_it(&mut self) -> i64 {
        assert!(self.v >= 0);
        self.v
    }
}

#[thrust_macros::requires(T::ok(*x))]
#[thrust_macros::ensures(true)]
fn f<T>(x: &mut T) -> i64
where
    T: Tr + thrust_models::Model,
{
    x.use_it()
}

fn main() {
    let mut p = P { v: 5 };
    let _ = f(&mut p);
}

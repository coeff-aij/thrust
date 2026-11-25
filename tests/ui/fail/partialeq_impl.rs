//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
use thrust_models::Model;
enum X {
    A(i32),
}

impl Model for X {
    type Ty = Self;
}

impl PartialEq for X {
    fn eq(&self, other: &X) -> bool {
        match (self, other) {
            (Self::A(lhs), Self::A(rhs)) => !lhs.eq(rhs),
        }
    }
}

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn rand() -> X {
    unimplemented!()
}

fn main() {
    let x = rand();
    assert!(x == x);
}

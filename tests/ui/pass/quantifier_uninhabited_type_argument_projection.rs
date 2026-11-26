//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off

// A field type is read at the ADT's arguments: `Outer<Y>`'s field `Option<I::A>` is
// `Option<u64>`.
use thrust_models::forall;

trait Tr {
    type A;
}

struct Y;

impl Tr for Y {
    type A = u64;
}

struct Outer<I: Tr> {
    h: Option<I::A>,
}

fn main() {
    let x = 0i64;
    thrust_macros::assume!(|x: i64| x == 0
        && forall(|o: Outer<Y>| match o { Outer { h: Some(_) } => true, Outer { h: None } => true }));
    assert!(x == 0);
}

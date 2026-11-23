//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off

// A variant no value is of has no constructor in its datatype, so no value of any sort is of it,
// however deeply it is nested (`E8::Bad` under eight enums) and inside a recursive enum's own
// payload (`L::Bad` under `L::Cons`). A `match` arm naming it is never taken.
use std::convert::Infallible;
use thrust_models::forall;

enum E0 { W(E1), Z }
enum E1 { W(E2), Z }
enum E2 { W(E3), Z }
enum E3 { W(E4), Z }
enum E4 { W(E5), Z }
enum E5 { W(E6), Z }
enum E6 { W(E7), Z }
enum E7 { W(E8), Z }
enum E8 { Bad(Infallible), Ok }

enum L {
    Nil,
    Cons(thrust_models::model::Box<L>),
    Bad(Infallible),
}

#[thrust_macros::ensures(forall(|e0: E0| match e0 { E0::W(e1) => match e1 { E1::W(e2) => match e2 { E2::W(e3) => match e3 { E3::W(e4) => match e4 { E4::W(e5) => match e5 { E5::W(e6) => match e6 { E6::W(e7) => match e7 { E7::W(e8) => match e8 { E8::Bad(_) => false, E8::Ok => true }, E7::Z => true }, E6::Z => true }, E5::Z => true }, E4::Z => true }, E3::Z => true }, E2::Z => true }, E1::Z => true }, E0::Z => true }))]
fn nested_variant_left_out() {}

#[thrust_macros::ensures(forall(|l: L| match l { L::Cons(b) => match *b { L::Bad(_) => false, L::Nil => true, L::Cons(_) => true }, L::Nil => true }))]
fn recursive_variant_left_out() {}

fn main() {
    let x = 0i64;
    thrust_macros::assume!(|x: i64| x == 0
        && forall(|l: L| match l { L::Cons(b) => match *b { L::Bad(_) => false, L::Nil => true, L::Cons(_) => true }, L::Nil => true }));
    assert!(x == 0);
}

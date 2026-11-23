//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A law's variable ranges over the values its proof assumes of the parameter, at every depth of
// its enum payloads: the proof of `absurd` reads the `u8` under nine enums, non-negative, so its
// premise is false of every value, and the law gives `tag` only where that premise is known.
use thrust_models::Model;

enum E0 { W(E1), Z }
enum E1 { W(E2), Z }
enum E2 { W(E3), Z }
enum E3 { W(E4), Z }
enum E4 { W(E5), Z }
enum E5 { W(E6), Z }
enum E6 { W(E7), Z }
enum E7 { W(E8), Z }
enum E8 { V(u8), Z }

impl Model for E0 { type Ty = Self; }
impl Model for E1 { type Ty = Self; }
impl Model for E2 { type Ty = Self; }
impl Model for E3 { type Ty = Self; }
impl Model for E4 { type Ty = Self; }
impl Model for E5 { type Ty = Self; }
impl Model for E6 { type Ty = Self; }
impl Model for E7 { type Ty = Self; }
impl Model for E8 { type Ty = Self; }

#[thrust_macros::context]
trait Absurd: Model
where
    <Self as Model>::Ty: Model<Ty = <Self as Model>::Ty>,
{
    #[thrust_macros::predicate]
    fn tag(self) -> bool;

    #[thrust_macros::law]
    #[thrust_macros::requires(match e { E0::W(e1) => match e1 { E1::W(e2) => match e2 { E2::W(e3) => match e3 { E3::W(e4) => match e4 { E4::W(e5) => match e5 { E5::W(e6) => match e6 { E6::W(e7) => match e7 { E7::W(e8) => match e8 { E8::V(x) => x < 0, _other => false }, _other => false }, _other => false }, _other => false }, _other => false }, _other => false }, _other => false }, _other => false }, _other => false })]
    #[thrust_macros::ensures(Self::tag(*a))]
    fn absurd(a: &Self, e: E0);
}

struct S(i64);

impl Model for S {
    type Ty = (thrust_models::model::Int,);
}

#[thrust_macros::context]
impl Absurd for S {
    #[thrust_macros::predicate]
    fn tag(self) -> bool {
        false
    }

    fn absurd(a: &S, e: E0) {
        if let E0::W(E1::W(E2::W(E3::W(E4::W(E5::W(E6::W(E7::W(E8::V(x))))))))) = e {
            let _y = x;
        }
    }
}

#[thrust_macros::context]
#[thrust_macros::requires(match e { E0::W(e1) => match e1 { E1::W(e2) => match e2 { E2::W(e3) => match e3 { E3::W(e4) => match e4 { E4::W(e5) => match e5 { E5::W(e6) => match e6 { E6::W(e7) => match e7 { E7::W(e8) => match e8 { E8::V(x) => x < 0, _other => false }, _other => false }, _other => false }, _other => false }, _other => false }, _other => false }, _other => false }, _other => false }, _other => false })]
#[thrust_macros::ensures(T::tag(*a))]
fn tagged<T: Absurd>(a: &T, e: E0)
where
    <T as Model>::Ty: Model<Ty = <T as Model>::Ty>,
{
}

fn main() {}

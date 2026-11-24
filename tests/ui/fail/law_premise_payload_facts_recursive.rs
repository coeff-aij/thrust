//@error-in-other-file: Unsat
//@ignore-on-host: not yet verifiable, the solver gives no answer within 280 s
//@compile-flags: -Adead_code -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A law's variable ranges over the values its proof assumes of the parameter, through a recursive
// enum's own payloads: the proof of `absurd` reads the second element of a list, non-negative, so
// its premise is false of every value, and the law gives `tag` only where that premise is known.
// The list is linked by references, which both a formula and the proof read through. The twin of
// `pass/law_premise_payload_facts_recursive.rs`, whose premise a list meets.
use thrust_models::Model;

enum L<'a> {
    Nil,
    Cons(u8, &'a L<'a>),
}

impl<'a> Model for L<'a> {
    type Ty = Self;
}

#[thrust_macros::context]
trait Absurd: Model
where
    <Self as Model>::Ty: Model<Ty = <Self as Model>::Ty>,
{
    #[thrust_macros::predicate]
    fn tag(self) -> bool;

    #[thrust_macros::law]
    #[thrust_macros::requires(match l { L::Cons(_, b) => match *b { L::Cons(x, _) => x < 0, L::Nil => false }, L::Nil => false })]
    #[thrust_macros::ensures(Self::tag(*a))]
    fn absurd(a: &Self, l: L<'static>);
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

    fn absurd(a: &S, l: L<'static>) {
        if let L::Cons(_, b) = l {
            if let L::Cons(x, _) = *b {
                let _y = x;
            }
        }
    }
}

#[thrust_macros::context]
#[thrust_macros::ensures(T::tag(*a))]
fn tagged<T: Absurd>(a: &T, l: L<'static>)
where
    <T as Model>::Ty: Model<Ty = <T as Model>::Ty>,
{
}

fn main() {}

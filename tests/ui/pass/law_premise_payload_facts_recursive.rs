//@check-pass
//@ignore-on-host: not yet verifiable, the solver gives no answer within 280 s
//@compile-flags: -Adead_code -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A law's variable ranges over the values of its type through a recursive enum's own payloads: a
// list whose second element is 1 is such a value, so the law gives `tag`. The list is linked by
// references, which a formula reads through. The twin of
// `fail/law_premise_payload_facts_recursive.rs`, whose premise no list meets.
use thrust_models::Model;

enum L<'a> {
    Nil,
    Cons(u8, &'a L<'a>),
}

impl<'a> Model for L<'a> {
    type Ty = Self;
}

#[thrust_macros::context]
trait Tagged: Model
where
    <Self as Model>::Ty: Model<Ty = <Self as Model>::Ty>,
{
    #[thrust_macros::predicate]
    fn tag(self) -> bool;

    #[thrust_macros::law]
    #[thrust_macros::requires(match l { L::Cons(_, b) => match *b { L::Cons(x, _) => x == 1, L::Nil => false }, L::Nil => false })]
    #[thrust_macros::ensures(Self::tag(*a))]
    fn by_second(a: &Self, l: L<'static>);
}

struct S(i64);

impl Model for S {
    type Ty = (thrust_models::model::Int,);
}

#[thrust_macros::context]
impl Tagged for S {
    #[thrust_macros::predicate]
    fn tag(self) -> bool {
        true
    }

    fn by_second(a: &S, l: L<'static>) {}
}

#[thrust_macros::context]
#[thrust_macros::ensures(T::tag(*a))]
fn tagged<T: Tagged>(a: &T)
where
    <T as Model>::Ty: Model<Ty = <T as Model>::Ty>,
{
}

fn main() {}

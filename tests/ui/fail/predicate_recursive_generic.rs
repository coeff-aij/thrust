//@compile-flags: -Adead_code -C debug-assertions=off

// `predicate_recursive` through a trait impl at a type parameter: at the instance `W<i64>` the
// call resolves to the predicate being defined, at the same type arguments. A call at other type
// arguments defines another predicate (`traits/nested_adapter_instance`).
use thrust_models::Model;

#[thrust_macros::context]
trait Liar {
    #[thrust_macros::predicate]
    fn liar(self) -> bool;
}

#[derive(PartialEq)]
struct W<T>(T);

impl<T: Model> Model for W<T> {
    type Ty = W<<T as Model>::Ty>;
}

#[thrust_macros::context]
impl<T> Liar for W<T>
where
    T: Model,
    <T as Model>::Ty: Model<Ty = <T as Model>::Ty> + PartialEq,
{
    #[thrust_macros::predicate]
    fn liar(self) -> bool {
        !<W<T> as Liar>::liar(self) //~ ERROR: a predicate cannot call itself
    }
}

#[thrust_macros::ensures(<W<i64> as Liar>::liar(w))]
fn f(w: W<i64>) {}

fn main() {
    f(W(0));
}

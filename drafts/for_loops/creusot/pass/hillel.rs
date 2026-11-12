//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables -A dead_code
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120
// Creusot's `insert_unique` and `unique` (`examples/hillel.rs`, 3620de437), with Creusot's code and
// Thrust's annotations: `for` loops over `vec.iter()` and `0..str.len()`, generic in the element
// type. Creusot's `T: DeepModel` is `T: Model + ModelEq` (`==` is equality of models), so
// `deep_model()` is the model itself.
use thrust_models::model::{Int, Seq, UInt};
use thrust_models::{exists, forall, FnParam, Ghost, Model, ModelEq};

#[thrust_macros::predicate]
fn is_unique<T: Model>(s: Seq<<T as Model>::Ty>) -> bool
where
    <T as Model>::Ty: Model<Ty = <T as Model>::Ty>,
{
    forall(|i: Int, j: Int| {
        !(0 <= i && i < s.len() && 0 <= j && j < s.len() && s[i] == s[j]) || i == j
    })
}

#[thrust_macros::predicate]
fn contains<T: Model>(seq: Seq<<T as Model>::Ty>, elem: <T as Model>::Ty) -> bool
where
    <T as Model>::Ty: Model<Ty = <T as Model>::Ty>,
{
    exists(|i: Int| 0 <= i && i < seq.len() && seq[i] == elem)
}

#[thrust_macros::predicate]
fn is_subset<T: Model>(sub: Seq<<T as Model>::Ty>, sup: Seq<<T as Model>::Ty>) -> bool
where
    <T as Model>::Ty: Model<Ty = <T as Model>::Ty>,
{
    forall(|i: Int| !(0 <= i && i < sub.len()) || contains::<T>(sup, sub[i]))
}

#[thrust_macros::context]
#[thrust_macros::requires(is_unique::<T>(*vec))]
#[thrust_macros::ensures(
    is_unique::<T>(!vec)
        && is_subset::<T>(*vec, !vec)
        && is_subset::<T>(!vec, (*vec).push(elem))
        && contains::<T>(!vec, elem)
)]
fn insert_unique<T: Eq + Model + ModelEq>(vec: &mut Vec<T>, elem: T)
where
    <T as Model>::Ty: Model<Ty = <T as Model>::Ty>,
{
    let v = vec;
    for e in v.iter() {
        thrust_macros::invariant!(|iter: core::slice::Iter<'_, T>, iter_old: Ghost<core::slice::Iter<'_, T>>, produced: Ghost<Seq<&<T as Model>::Ty>>, v: &mut Vec<T>, vec: FnParam<&mut Vec<T>>, elem: T|
            iter_old.0 == *v && iter_old.1 == 0 && *v == *vec.at_entry() && !v == !vec.at_entry() && is_unique::<T>(*v)
                && forall(|j: Int| !(0 <= j && j < produced.len()) || *produced[j] != elem));
        if e == &elem {
            return;
        }
    }
    thrust_macros::proof_assert!(|v: &mut Vec<T>, elem: T| is_unique::<T>((*v).push(elem)));
    v.push(elem);
}

#[thrust_macros::context]
#[thrust_macros::ensures(
    is_unique::<T>(result)
        && is_subset::<T>(result, *str)
        && is_subset::<T>(*str, result)
)]
fn unique<T: Eq + Model + ModelEq + Copy>(str: &[T]) -> Vec<T>
where
    <T as Model>::Ty: Model<Ty = <T as Model>::Ty>,
{
    let mut unique = Vec::new();

    for i in 0..str.len() {
        thrust_macros::invariant!(|iter: core::ops::Range<usize>, iter_old: Ghost<core::ops::Range<usize>>, produced: Ghost<Seq<UInt>>, unique: Vec<T>, str: &[T]|
            iter_old.start == 0 && iter_old.end == (*str).len()
                && is_unique::<T>(unique)
                && is_subset::<T>(unique, *str)
                && is_subset::<T>((*str).subsequence(0, produced.len()), unique));
        let elem: T = str[i];
        insert_unique(&mut unique, elem);
    }

    unique
}

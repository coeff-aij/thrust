//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables -A dead_code
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300

// The fail twin of flatten_next.rs: an inner iterator taken from the outer one is discarded.
// std's `FlattenCompat::next` (core/src/iter/adapters/flatten.rs, toolchain 1.94.1), the loop that
// takes the next item from the front inner iterator and, when it is exhausted, the next inner
// iterator from the outer one. Deviations: no `backiter` (the `None` arm returns `None` where std
// takes from the back iterator, which only `next_back` fills), the outer items are the inner
// iterators (std's `into_iter` of an `IntoIterator`), and `and_then_or_clear` is specialised to
// `Iterator::next` with a `match` for `opt.as_mut()?`. The contract is a step of the adapter, not an
// `IteratorSpec` impl: an item comes from the front iterator, or from a fresh inner iterator after
// some that were empty; `None` means the outer iterator completed after inner iterators that were
// all empty. Every inner iterator is assumed to keep `inv` (as Creusot's `Filter` assumes its
// predicate has no precondition).
use thrust_models::model::{Int, Mut, Seq};
use thrust_models::{exists, forall, Ghost, Model};

// `u` returns `None` at once.
#[thrust_macros::predicate]
fn empty<U>(u: U) -> bool
where
    U: IteratorSpec,
    U::Item: Model,
{
    exists(|u2: <U as Model>::Ty| U::completed(Mut::new(u, u2)))
}

// Every inner iterator of `us` is empty.
#[thrust_macros::predicate]
fn all_empty<U>(us: Seq<<U as Model>::Ty>) -> bool
where
    U: IteratorSpec,
    U::Item: Model,
{
    forall(|k: Int| !(0 <= k && k < us.len()) || empty::<U>(us[k]))
}

#[thrust_macros::context]
#[thrust_macros::requires(forall(|u: <U as Model>::Ty| U::inv(u)))]
#[thrust_macros::ensures(*opt == None ==> (result == None && !opt == None))]
#[thrust_macros::ensures(forall(|u: <U as Model>::Ty| *opt == Some(u) ==> exists(|u2: <U as Model>::Ty|
    (result == None && U::completed(Mut::new(u, u2)) && !opt == None)
        || exists(|x: <U::Item as Model>::Ty| result == Some(x) && U::produces(u, Seq::singleton(x), u2) && !opt == Some(u2)))))]
fn and_then_or_clear<U: IteratorSpec>(opt: &mut Option<U>) -> Option<U::Item>
where
    U::Item: Model,
{
    let x = match opt {
        Some(u) => u.next(),
        None => return None,
    };
    if x.is_none() {
        *opt = None;
    }
    x
}

struct Flatten<I, U> {
    iter: I,
    frontiter: Option<U>,
}

impl<I: Model, U: Model> Model for Flatten<I, U> {
    type Ty = Flatten<<I as Model>::Ty, <U as Model>::Ty>;
}

#[thrust_macros::context]
#[thrust_macros::requires(I::inv((*this).iter))]
#[thrust_macros::requires(forall(|u: <U as Model>::Ty| U::inv(u)))]
#[thrust_macros::ensures(I::inv((!this).iter))]
#[thrust_macros::ensures(forall(|x: <U::Item as Model>::Ty| result == Some(x) ==>
    (exists(|f: <U as Model>::Ty, f2: <U as Model>::Ty|
        (*this).frontiter == Some(f) && U::produces(f, Seq::singleton(x), f2)
            && (!this).frontiter == Some(f2) && (!this).iter == (*this).iter)
    || exists(|us: Seq<<U as Model>::Ty>, u: <U as Model>::Ty, u2: <U as Model>::Ty|
        I::produces((*this).iter, us.push(u), (!this).iter) && all_empty::<U>(us)
            && U::produces(u, Seq::singleton(x), u2) && (!this).frontiter == Some(u2)))))]
#[thrust_macros::ensures(result == None ==> exists(|us: Seq<<U as Model>::Ty>, mid: <I as Model>::Ty|
    I::produces((*this).iter, us, mid) && I::completed(Mut::new(mid, (!this).iter)) && all_empty::<U>(us)
        && (!this).frontiter == None))]
fn flatten_next<I, U>(this: &mut Flatten<I, U>) -> Option<U::Item>
where
    I: IteratorSpec<Item = U>,
    U: IteratorSpec,
    U::Item: Model,
{
    let old = thrust_macros::ghost!(|this: &mut Flatten<I, U>| -> Flatten<I, U> { *this });
    I::produces_refl(&this.iter);
    loop {
        thrust_macros::partial_invariant!(|this: &mut Flatten<I, U>, old: Ghost<Flatten<I, U>>|
            I::inv((*this).iter)
                && (((*this).frontiter == old.frontiter && (*this).iter == old.iter)
                || (exists(|us: Seq<<U as Model>::Ty>, u: <U as Model>::Ty|
                    I::produces(old.iter, us.push(u), (*this).iter) && all_empty::<U>(us)
                        && (*this).frontiter == Some(u))
                    && (old.frontiter == None || exists(|f: <U as Model>::Ty| old.frontiter == Some(f) && empty::<U>(f))))));
        if let elt @ Some(_) = and_then_or_clear(&mut this.frontiter) {
            return elt;
        }
        match this.iter.next() {
            None => return None,
            Some(inner) => this.frontiter = None,
        }
    }
}

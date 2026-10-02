//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off -A unused-variables -A unused_parens -A unused_imports
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300 THRUST_TRY_SPECS=1

use std::marker::PhantomData;
use thrust_models::model::{Closure, Int, Mut, Seq, UInt};
use thrust_models::{exists, forall, Ghost};

// The iterator trait, local to the case study (rewrites.md R9): Creusot's `common.rs` as the
// Creusot benchmark cases of the fork declare it (tests/ui/pass/creusot/range.rs), with the
// predicates `produces`, `completed` and `invariant` (`true` unless the impl says otherwise), the
// laws `produces_refl` and `produces_trans`, which every impl inherits and Thrust checks at each
// impl, and `next` with Creusot's contract. It shadows std's `Iterator`.
#[thrust_macros::context]
trait Iterator
where
    Self: thrust_models::Model,
    Self::Item: thrust_models::Model,
{
    type Item;

    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as thrust_models::Model>::Ty>, o: Self) -> bool;

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool;

    #[thrust_macros::law]
    #[thrust_macros::requires(Self::invariant(*a))]
    #[thrust_macros::ensures(Self::produces(*a, Seq::empty(), *a))]
    fn produces_refl(a: &Self) {}

    #[thrust_macros::law]
    #[thrust_macros::requires(Self::produces(*a, ab, *b))]
    #[thrust_macros::requires(Self::produces(*b, bc, *c))]
    #[thrust_macros::ensures(Self::produces(*a, ab.concat(bc), *c))]
    fn produces_trans(
        a: &Self,
        ab: Seq<<Self::Item as thrust_models::Model>::Ty>,
        b: &Self,
        bc: Seq<<Self::Item as thrust_models::Model>::Ty>,
        c: &Self,
    ) {
    }

    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        true
    }

    #[thrust_macros::requires(Self::invariant(*self))]
    #[thrust_macros::ensures(Self::invariant(!self))]
    #[thrust_macros::ensures(result == None ==> Self::completed(self))]
    #[thrust_macros::ensures(forall(|i| result == Some(i) ==> Self::produces(*self, Seq::singleton(i), !self)))]
    fn next(&mut self) -> Option<Self::Item>;
}

pub struct IndexVec<I, T> {
    raw: Vec<T>,
    _marker: PhantomData<fn(&I)>,
}

impl<I, T: thrust_models::Model> thrust_models::Model for IndexVec<I, T> {
    type Ty = <[T] as thrust_models::Model>::Ty;
}


pub struct DenseBitSet {
    words: Vec<u64>,
}

impl thrust_models::Model for DenseBitSet {
    type Ty = UInt;
}

pub struct BitIter {
    word: u64,
}

impl thrust_models::Model for BitIter {
    type Ty = UInt;
}

#[thrust_macros::context]
impl DenseBitSet {
    #[thrust::trusted]
    #[thrust::callable]
    #[thrust_macros::ensures(result == *self)]
    fn iter(&self) -> BitIter {
        BitIter { word: 0 }
    }
}

#[thrust_macros::context]
impl Iterator for BitIter {
    type Item = usize;

    fn next(&mut self) -> Option<usize> {
        self.next_bit()
    }

    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        true
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as thrust_models::Model>::Ty>, o: Self) -> bool {
        o + visited.len() == self
            && forall(|i: Int| !(0 <= i && i < visited.len()) || 0 <= visited[i])
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        *self == 0 && *self == !self
    }
}

// The trusted stub behind `next`: Thrust trusts a function only on its own contract, and the
// method of an impl of the local trait has the trait's.
#[thrust_macros::context]
impl BitIter {
    #[thrust::trusted]
    #[thrust_macros::requires(<Self as Iterator>::invariant(*self))]
    #[thrust_macros::ensures(
        <Self as Iterator>::invariant(!self)
            && (result == None ==> <Self as Iterator>::completed(self))
            && forall(|x: <usize as thrust_models::Model>::Ty| result == Some(x) ==> <Self as Iterator>::produces(*self, Seq::singleton(x), !self))
    )]
    fn next_bit(&mut self) -> Option<usize> {
        None
    }
}
// Rewrite (rewrites.md R8): a local `Map` in place of `iter::Map`, evaluation 1's adapter
// (tests/ui/pass/creusot/map.rs) on the local `Iterator`. The model is the inner iterator and
// the closure state; `produces` carries the input items `s` and the chain `fs` of closure states.
struct Map<I, F> {
    iter: I,
    func: F,
}

impl<I: thrust_models::Model, F> thrust_models::Model for Map<I, F> {
    type Ty = (<I as thrust_models::Model>::Ty, Closure<F>);
}

// Creusot's `next_precondition`, `preservation_inv`, `reinitialize` and `produces`, and the lemma
// that proves `produces_trans`.
#[thrust_macros::context]
impl<I, B, F> Map<I, F>
where
    I: Iterator,
    B: thrust_models::Model,
    F: FnMut(I::Item) -> B,
    I::Item: thrust_models::Model,
    <I::Item as thrust_models::Model>::Ty: PartialEq,
    <I as thrust_models::Model>::Ty: PartialEq,
    <B as thrust_models::Model>::Ty: PartialEq,
{
    #[thrust_macros::requires(
        I::invariant(iter)
            && Self::reinitialize()
            && Self::preservation_inv(iter, func)
            && Self::next_precondition(iter, func)
    )]
    #[thrust_macros::ensures(result.0 == iter && result.1 == func)]
    fn new(iter: I, func: F) -> Map<I, F> {
        Map { iter, func }
    }

    #[thrust_macros::predicate]
    fn next_precondition(iter: I, func: F) -> bool {
        forall(|e: <I::Item as thrust_models::Model>::Ty| forall(|i: <I as thrust_models::Model>::Ty|
            !I::produces(iter, Seq::singleton(e), i) || thrust_macros::pre!(func(e))))
    }

    #[thrust_macros::predicate]
    fn preservation_inv(iter: I, func: F) -> bool {
        forall(|s: Seq<<I::Item as thrust_models::Model>::Ty>|
        forall(|e1: <I::Item as thrust_models::Model>::Ty|
        forall(|e2: <I::Item as thrust_models::Model>::Ty|
        forall(|i: <I as thrust_models::Model>::Ty|
        forall(|f1: Closure<F>|
        forall(|f2: Closure<F>|
        forall(|b: <B as thrust_models::Model>::Ty|
            !(thrust_macros::hist_inv!(func, f1)
                && I::produces(iter, s.push(e1).push(e2), i)
                && thrust_macros::pre!(f1(e1))
                && thrust_macros::post!(Mut::new(f1, f2)(e1), b))
                || thrust_macros::pre!(f2(e2)))))))))
    }

    #[thrust_macros::predicate]
    fn reinitialize() -> bool {
        forall(|cur: <I as thrust_models::Model>::Ty| forall(|fin: <I as thrust_models::Model>::Ty| forall(|f: Closure<F>|
            !I::completed(Mut::new(cur, fin))
                || (Self::next_precondition(fin, f)
                    && Self::preservation_inv(fin, f)))))
    }

    #[thrust_macros::predicate]
    fn produces_at(s0: Self, visited: Vec<B>, o: Self, s: Seq<<I::Item as thrust_models::Model>::Ty>, fs: Seq<F>) -> bool {
        thrust_macros::hist_inv!(s0.1, o.1)
            && s.len() == visited.len()
            && I::produces(s0.0, s, o.0)
            && fs.len() == visited.len() + 1
            && fs[0] == s0.1
            && fs[visited.len()] == o.1
            && forall(|k: Int|
                !(0 <= k && k < visited.len())
                    || (thrust_macros::hist_inv!(s0.1, fs[k])
                        && thrust_macros::post!(Mut::new(fs[k], fs[k + 1])(s[k]), visited[k])))
    }

    // `produces_at` of the joined witnesses: the input items concatenated and the closure states
    // joined at their shared state.
    #[thrust_macros::ensures(forall(|sab: Seq<<I::Item as thrust_models::Model>::Ty>| forall(|sbc: Seq<<I::Item as thrust_models::Model>::Ty>|
        forall(|fab: Seq<Closure<F>>| forall(|fbc: Seq<Closure<F>>|
        !(Self::produces_at(a, ab, b, sab, fab) && Self::produces_at(b, bc, c, sbc, fbc))
            || Self::produces_at(a, ab.concat(bc), c, sab.concat(sbc), fab.subsequence(0, ab.len()).concat(fbc)))))))]
    fn produces_trans_at(
        a: Ghost<Self>,
        ab: Ghost<Seq<<B as thrust_models::Model>::Ty>>,
        b: Ghost<Self>,
        bc: Ghost<Seq<<B as thrust_models::Model>::Ty>>,
        c: Ghost<Self>,
    ) {
    }
}

#[thrust_macros::context]
impl<I, B, F> Iterator for Map<I, F>
where
    I: Iterator,
    B: thrust_models::Model,
    F: FnMut(I::Item) -> B,
    I::Item: thrust_models::Model,
    <I::Item as thrust_models::Model>::Ty: PartialEq,
    <I as thrust_models::Model>::Ty: PartialEq,
    <B as thrust_models::Model>::Ty: PartialEq,
{
    type Item = B;

    fn next(&mut self) -> Option<B> {
        let pre = thrust_macros::ghost!(|self: &mut Self| -> Self { *self });
        let r = self.iter.next();
        match r {
            Some(v) => {
                let e = thrust_macros::ghost!(|v: <I as Iterator>::Item| -> <I as Iterator>::Item { v });
                let b = (self.func)(v);
                let post = thrust_macros::ghost!(|self: &mut Self| -> Self { *self });
                let bm = thrust_macros::ghost!(|b: B| -> B { b });
                // Keeps `self` live at the snapshot `post`.
                let _keep = &*self;
                Some(b)
            }
            None => None,
        }
    }

    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        Self::reinitialize()
            && Self::preservation_inv(self.0, self.1)
            && I::invariant(self.0)
            && Self::next_precondition(self.0, self.1)
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as thrust_models::Model>::Ty>, o: Self) -> bool {
        thrust_macros::hist_inv!(self.1, o.1)
            && exists(|s: Seq<<I::Item as thrust_models::Model>::Ty>| exists(|fs: Seq<Closure<F>>|
                Self::produces_at(self, visited, o, s, fs)))
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        I::completed(Mut::new((*self).0, (!self).0))
            && (*self).1 == (!self).1
    }

    fn produces_trans(
        a: &Self,
        ab: Seq<<Self::Item as thrust_models::Model>::Ty>,
        b: &Self,
        bc: Seq<<Self::Item as thrust_models::Model>::Ty>,
        c: &Self,
    ) {
        let ga = thrust_macros::ghost!(|a: &Self| -> Self { *a });
        let gb = thrust_macros::ghost!(|b: &Self| -> Self { *b });
        let gc = thrust_macros::ghost!(|c: &Self| -> Self { *c });
        let gab = thrust_macros::ghost!(|ab: Seq<<B as thrust_models::Model>::Ty>| -> Seq<<B as thrust_models::Model>::Ty> { ab });
        let gbc = thrust_macros::ghost!(|bc: Seq<<B as thrust_models::Model>::Ty>| -> Seq<<B as thrust_models::Model>::Ty> { bc });
        Self::produces_trans_at(ga, gab, gb, gbc, gc);
        // Keeps the parameters live at the snapshots above.
        let _live = (a, &ab, b, &bc, c);
    }
}

// Rewrite (rewrites.md R8): `collect` into a `Result` of an `IndexVec`, in place of the
// `FromIterator for Result<V, E>` of std: the first `Err` item is returned; otherwise the
// collection holds the `Ok` payloads of what the iterator produced before it completed.
#[thrust_macros::context]
#[thrust_macros::requires(J::invariant(iter))]
#[thrust_macros::ensures(
    forall(|v: <IndexVec<I, T> as thrust_models::Model>::Ty| result != Ok(v)
        || exists(|visited: Seq<<Result<T, E> as thrust_models::Model>::Ty>,
                   mid: <J as thrust_models::Model>::Ty,
                   fin: <J as thrust_models::Model>::Ty|
            J::produces(iter, visited, mid)
                && J::completed(Mut::new(mid, fin))
                && visited.len() == v.len()
                && forall(|k: Int| !(0 <= k && k < v.len()) || visited[k] == Ok(v[k]))))
)]
fn collect_index_vec_result<I, T, E, J>(iter: J) -> Result<IndexVec<I, T>, E>
where
    T: thrust_models::Model,
    T::Ty: PartialEq,
    E: thrust_models::Model,
    E::Ty: PartialEq,
    J: Iterator<Item = Result<T, E>>,
    <J as thrust_models::Model>::Ty: PartialEq,
{
    let mut it = iter;
    J::produces_refl(&it);
    let mut v: Vec<T> = Vec::new();
    while let Some(x) = it.next() {
        thrust_macros::invariant!(
            |it: J, v: Vec<T>, iter: thrust_models::FnParam<J>|
                J::invariant(it)
                    && exists(|s: Seq<<Result<T, E> as thrust_models::Model>::Ty>|
                        J::produces(iter.at_entry(), s, it)
                            && s.len() == v.len()
                            && forall(|k: Int| !(0 <= k && k < v.len()) || s[k] == Ok(v[k])))
        );
        match x {
            Ok(y) => v.push(y),
            Err(e) => return Err(e),
        }
    }
    Ok(IndexVec {
        raw: v,
        _marker: PhantomData,
    })
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    forall(|v: <IndexVec<u8, usize> as thrust_models::Model>::Ty|
        result != Ok(v) || (v.len() == *set + 1 && forall(|k: Int| !(0 <= k && k < v.len()) || 0 <= v[k])))
)]
fn collect_bits(set: &DenseBitSet) -> Result<IndexVec<u8, usize>, u32> {
    collect_index_vec_result::<u8, usize, u32, _>(Map::new(
        set.iter(),
        thrust_macros::closure!(requires(true), ensures(result == Ok(i)), |i: usize| -> Result<usize, u32> { Ok(i) }),
    ))
}

fn main() {}

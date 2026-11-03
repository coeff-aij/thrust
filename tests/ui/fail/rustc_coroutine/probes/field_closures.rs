//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off -A unused-variables -A unused_parens -A unused_imports -A unexpected_cfgs
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300 THRUST_TRY_SPECS=1
//@rustc-env: THRUST_SPLIT=1 THRUST_SPLIT_GOALS=1

// layout.rs's `univariant_biased` reduced to its closures over the fields: the two `Map`s whose
// maxima give `max_field_align` and `largest_niche_size`, over the fields without the tail, and
// the `Filter` of the non-ZST fields over `iter_enumerated`, whose first two items are read. The
// adapters are copies of thrust/iter.rs's; `IterEnumerated` is rustc_index's with a `usize`
// index. A field is an `F` that dereferences to its layout, as in layout.rs, and the requires
// are the conjuncts of `layout_pre` the closures and the items read rely on: the niche of every
// field is well formed (`available` asserts its size), and so is the scalar of every scalar
// field (`scalar_pair` requires it).
//
// The filter's items are used as indices into `offsets` and as fields whose scalars are paired,
// so `Filter::next` states, besides the trait's contract, that the item it returns is the last
// one the inner iterator produced in that call. thrust/iter.rs's `Filter::produces` states only
// the count.

use std::ops::Deref;
use thrust_models::model::{Closure, Int, Mut, Seq, UInt};
use thrust_models::{exists, forall, Ghost};

#[derive(Clone, Copy, PartialEq)]
enum Primitive {
    Int(u64),
    Pointer,
}

impl thrust_models::Model for Primitive {
    type Ty = Self;
}

#[derive(Clone, Copy, PartialEq)]
struct Dl {
    pointer_bytes: u64,
}

impl thrust_models::Model for Dl {
    type Ty = Self;
}

#[derive(Clone, Copy, PartialEq)]
struct Niche {
    offset: u64,
    value: Primitive,
    range: u128,
}

impl thrust_models::Model for Niche {
    type Ty = Self;
}

#[derive(Clone, Copy, PartialEq)]
enum BackendRepr {
    Scalar(Primitive),
    Memory { sized: bool },
}

impl thrust_models::Model for BackendRepr {
    type Ty = Self;
}

#[derive(Clone, Copy, PartialEq)]
struct LayoutData {
    align: u64,
    size: u64,
    largest_niche: Option<Niche>,
    backend_repr: BackendRepr,
}

impl thrust_models::Model for LayoutData {
    type Ty = Self;
}

#[thrust_macros::context]
impl Primitive {
    // A primitive is at most 16 bytes under `dl` (lib.rs's `Niche::wf_in` and `Scalar::wf_in`).
    #[thrust_macros::predicate]
    fn wf_in(self, dl: Dl) -> bool {
        (self != Primitive::Pointer || dl.pointer_bytes <= 16)
            && forall(|b: u64| self != Primitive::Int(b) || b <= 16)
    }
}

#[thrust_macros::context]
impl Niche {
    // lib.rs's `available` asserts that the niche's primitive is at most 128 bits.
    #[thrust_macros::requires(Primitive::wf_in((*self).value, *dl))]
    #[thrust_macros::ensures(true)]
    fn available(&self, dl: &Dl) -> u128 {
        let size = match self.value {
            Primitive::Int(b) => b,
            Primitive::Pointer => dl.pointer_bytes,
        };
        assert!(size <= 16);
        self.range
    }
}

impl LayoutData {
    fn is_zst(&self) -> bool {
        match self.backend_repr {
            BackendRepr::Scalar(_) => false,
            BackendRepr::Memory { sized } => sized && self.size == 0,
        }
    }
}

// Trusted, as simple.rs's `scalar_pair` is; the `requires` is its panic condition.
#[thrust::trusted]
#[thrust_macros::requires(Primitive::wf_in(a, *dl) && Primitive::wf_in(b, *dl))]
#[thrust_macros::ensures(true)]
fn scalar_pair(dl: &Dl, a: Primitive, b: Primitive) -> u64 {
    0
}

// `max` as thrust/std_specs.rs gives it.
#[thrust::extern_spec_fn]
#[thrust_macros::requires(I::inv(it))]
#[thrust_macros::ensures(true)]
fn _extern_spec_iterator_max<I>(it: I) -> Option<I::Item>
where
    I: IteratorSpec,
    I::Item: thrust_models::Model + Ord,
{
    <I as Iterator>::max(it)
}

// rustc_index's `IterEnumerated` with a `usize` index: yields `(0, &raw[0])`, ...,
// `(len - 1, &raw[len - 1])`.
struct IterEnumerated<'a, T> {
    raw: &'a [T],
    pos: usize,
}

impl<'a, T: thrust_models::Model> thrust_models::Model for IterEnumerated<'a, T> {
    type Ty = (&'a Seq<<T as thrust_models::Model>::Ty>, UInt);
}

#[thrust_macros::context]
impl<'a, T: thrust_models::Model> Iterator for IterEnumerated<'a, T> {
    type Item = (usize, &'a T);

    fn next(&mut self) -> Option<(usize, &'a T)> {
        if self.pos < self.raw.len() {
            let n = self.pos;
            self.pos += 1;
            Some((n, &self.raw[n]))
        } else {
            None
        }
    }
}

#[thrust_macros::context]
impl<'a, T: thrust_models::Model> IteratorSpec for IterEnumerated<'a, T> {
    #[thrust_macros::predicate]
    fn inv(self) -> bool {
        0 <= self.1 && self.1 <= self.0.len()
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Vec<Self::Item>, o: Self) -> bool {
        self.0 == o.0
            && self.1 <= o.1
            && o.1 <= self.0.len()
            && visited.len() == o.1 - self.1
            && forall(|i: UInt| !(0 <= i && i < visited.len())
                || (visited[i].0 == self.1 + i && visited[i].1 == &self.0[self.1 + i]))
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        (*self).1 >= (*self).0.len() && *self == !self
    }

    fn produces_refl(a: &Self) {}

    fn produces_trans(
        a: &Self,
        ab: Seq<<Self::Item as thrust_models::Model>::Ty>,
        b: &Self,
        bc: Seq<<Self::Item as thrust_models::Model>::Ty>,
        c: &Self,
    ) {
    }
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(*result.0 == *raw && result.1 == 0)]
fn iter_enumerated<'a, T: thrust_models::Model>(raw: &'a [T]) -> IterEnumerated<'a, T> {
    IterEnumerated { raw, pos: 0 }
}

// thrust/iter.rs's `Map`.
struct Map<I, F> {
    iter: I,
    func: F,
}

impl<I: thrust_models::Model, F> thrust_models::Model for Map<I, F> {
    type Ty = (<I as thrust_models::Model>::Ty, Closure<F>);
}

#[thrust_macros::context]
impl<I, B, F> Map<I, F>
where
    I: IteratorSpec,
    B: thrust_models::Model,
    F: FnMut(I::Item) -> B,
    I::Item: thrust_models::Model,
{
    #[thrust_macros::requires(
        I::inv(iter)
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
            && forall(|k: UInt|
                !(0 <= k && k < visited.len())
                    || (thrust_macros::hist_inv!(s0.1, fs[k])
                        && thrust_macros::post!(Mut::new(fs[k], fs[k + 1])(s[k]), visited[k])))
    }

    #[thrust_macros::ensures(forall(|sab: Seq<<I::Item as thrust_models::Model>::Ty>| forall(|sbc: Seq<<I::Item as thrust_models::Model>::Ty>|
        forall(|fab: Seq<Closure<F>>| forall(|fbc: Seq<Closure<F>>|
        Self::produces_at(a, ab, b, sab, fab) && Self::produces_at(b, bc, c, sbc, fbc) ==> Self::produces_at(a, ab.concat(bc), c, sab.concat(sbc), fab.subsequence(0, ab.len()).concat(fbc)))))))]
    #[thrust_macros::lemma]
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
    I: IteratorSpec,
    B: thrust_models::Model,
    F: FnMut(I::Item) -> B,
    I::Item: thrust_models::Model,
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
}

#[thrust_macros::context]
impl<I, B, F> IteratorSpec for Map<I, F>
where
    I: IteratorSpec,
    B: thrust_models::Model,
    F: FnMut(I::Item) -> B,
    I::Item: thrust_models::Model,
{
    #[thrust_macros::predicate]
    fn inv(self) -> bool {
        Self::reinitialize()
            && Self::preservation_inv(self.0, self.1)
            && I::inv(self.0)
            && Self::next_precondition(self.0, self.1)
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Vec<Self::Item>, o: Self) -> bool {
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

    fn produces_refl(a: &Self) {}
}

// thrust/iter.rs's `Filter`, with `next`'s contract of its own.
struct Filter<I, P> {
    iter: I,
    predicate: P,
}

impl<I: thrust_models::Model, P> thrust_models::Model for Filter<I, P> {
    type Ty = (<I as thrust_models::Model>::Ty, Closure<P>);
}

#[thrust_macros::context]
impl<I, P> Filter<I, P>
where
    I: IteratorSpec,
    P: Fn(&I::Item) -> bool,
    I::Item: thrust_models::Model,
{
    #[thrust_macros::requires(
        I::inv(iter)
            && Self::reinitialize()
            && Self::pre_all(iter, predicate)
    )]
    #[thrust_macros::ensures(result.0 == iter && result.1 == predicate)]
    fn new(iter: I, predicate: P) -> Filter<I, P> {
        Filter { iter, predicate }
    }

    #[thrust_macros::predicate]
    fn pre_all(iter: I, func: P) -> bool {
        forall(|s: Seq<<I::Item as thrust_models::Model>::Ty>|
        forall(|e: <I::Item as thrust_models::Model>::Ty|
        forall(|i: <I as thrust_models::Model>::Ty|
            !I::produces(iter, s.push(e), i) || thrust_macros::pre!(func(&e)))))
    }

    #[thrust_macros::predicate]
    fn reinitialize() -> bool {
        forall(|cur: <I as thrust_models::Model>::Ty| forall(|fin: <I as thrust_models::Model>::Ty|
            !I::completed(Mut::new(cur, fin))
                || forall(|f: Closure<P>| Self::pre_all(fin, f))))
    }

    #[thrust_macros::predicate]
    fn pre_ok(a: Self) -> bool {
        Self::pre_all(a.0, a.1)
    }

    #[thrust_macros::predicate]
    fn stepped(a: Self, x: I::Item, b: Self) -> bool {
        Self::pre_ok(a) && I::produces(a.0, Seq::singleton(x), b.0) && a.1 == b.1
    }

    #[thrust_macros::requires(Self::stepped(a, x, b))]
    #[thrust_macros::ensures(Self::pre_ok(b))]
    fn pre_all_step(a: Ghost<Self>, x: Ghost<I::Item>, b: Ghost<Self>) {}

    #[thrust_macros::predicate]
    fn produces_at(s0: Self, visited: Vec<I::Item>, o: Self, s: Seq<<I::Item as thrust_models::Model>::Ty>) -> bool {
        s0.1 == o.1
            && I::produces(s0.0, s, o.0)
            && visited.len() <= s.len()
    }

    #[thrust_macros::ensures(forall(|sab: Seq<<I::Item as thrust_models::Model>::Ty>| forall(|sbc: Seq<<I::Item as thrust_models::Model>::Ty>|
        Self::produces_at(a, ab, b, sab) && Self::produces_at(b, bc, c, sbc) ==> Self::produces_at(a, ab.concat(bc), c, sab.concat(sbc)))))]
    #[thrust_macros::lemma]
    fn produces_trans_at(
        a: Ghost<Self>,
        ab: Ghost<Seq<<I::Item as thrust_models::Model>::Ty>>,
        b: Ghost<Self>,
        bc: Ghost<Seq<<I::Item as thrust_models::Model>::Ty>>,
        c: Ghost<Self>,
    ) {
    }
}

#[thrust_macros::context]
impl<I, P> Iterator for Filter<I, P>
where
    I: IteratorSpec,
    P: Fn(&I::Item) -> bool,
    I::Item: thrust_models::Model,
{
    type Item = I::Item;

    // The trait's contract, and the item returned is the last the inner iterator produced.
    #[thrust_macros::requires(<Self as IteratorSpec>::inv(*self))]
    #[thrust_macros::ensures(
        <Self as IteratorSpec>::inv(!self)
            && (result == None ==> <Self as IteratorSpec>::completed(self))
            && forall(|x: <I::Item as thrust_models::Model>::Ty| result == Some(x)
                ==> (<Self as IteratorSpec>::produces(*self, Seq::singleton(x), !self)
                    && exists(|s: Seq<<I::Item as thrust_models::Model>::Ty>|
                        I::produces((*self).0, s.push(x), (!self).0))))
    )]
    fn next(&mut self) -> Option<I::Item> {
        let this = self;
        let mut skipped: Vec<I::Item> = Vec::new();
        loop {
            thrust_macros::invariant!(
                |this: &mut Filter<I, P>, skipped: Vec<I::Item>, self: thrust_models::FnParam<&mut Filter<I, P>>|
                    !this == !self.at_entry()
                        && Filter::<I, P>::reinitialize()
                        && Filter::<I, P>::pre_all((*this).0, (*this).1)
                        && I::inv((*this).0)
                        && (*this).1 == (*self.at_entry()).1
                        && I::produces((*self.at_entry()).0, skipped, (*this).0)
            );
            let before = thrust_macros::ghost!(|this: &mut Filter<I, P>| -> Filter<I, P> { *this });
            let Some(x) = this.iter.next() else {
                break;
            };
            let yielded = thrust_macros::ghost!(|x: I::Item| -> I::Item { x });
            let after = thrust_macros::ghost!(|this: &mut Filter<I, P>| -> Filter<I, P> { *this });
            Filter::<I, P>::pre_all_step(before, yielded, after);
            if (this.predicate)(&x) {
                return Some(x);
            }
            skipped.push(x);
        }
        None
    }
}

#[thrust_macros::context]
impl<I, P> IteratorSpec for Filter<I, P>
where
    I: IteratorSpec,
    P: Fn(&I::Item) -> bool,
    I::Item: thrust_models::Model,
{
    #[thrust_macros::predicate]
    fn inv(self) -> bool {
        Self::reinitialize()
            && I::inv(self.0)
            && Self::pre_all(self.0, self.1)
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Vec<Self::Item>, o: Self) -> bool {
        exists(|s: Seq<<I::Item as thrust_models::Model>::Ty>|
            Self::produces_at(self, visited, o, s))
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        (*self).1 == (!self).1
            && exists(|s: Seq<<I::Item as thrust_models::Model>::Ty>| exists(|mid: <I as thrust_models::Model>::Ty|
                I::produces((*self).0, s, mid)
                    && I::completed(Mut::new(mid, (!self).0))))
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
        let gab = thrust_macros::ghost!(|ab: Seq<<I::Item as thrust_models::Model>::Ty>| -> Seq<<I::Item as thrust_models::Model>::Ty> { ab });
        let gbc = thrust_macros::ghost!(|bc: Seq<<I::Item as thrust_models::Model>::Ty>| -> Seq<<I::Item as thrust_models::Model>::Ty> { bc });
        Self::produces_trans_at(ga, gab, gb, gbc, gc);
        // Keeps the parameters live at the snapshots above.
        let _live = (a, &ab, b, &bc, c);
    }

    fn produces_refl(a: &Self) {}
}

// `univariant_biased`'s closures over the fields. `end` and `fields_excluding_tail` are its own;
// `offsets` stands for the offsets it computed, one per field. The closures' contracts are
// written: the niche closure requires what `available` needs of the niche of its field's layout,
// and the others require nothing. The filter closure takes its argument as `p` rather than by the
// pattern `&(_, f)`, which a `closure!` clause does not accept.
#[thrust_macros::requires(!maybe_unsized || (*fields).len() > 0)]
#[thrust_macros::requires((*offsets).len() == (*fields).len())]
// Broken: the niche of the last field is not required well formed, and a sized struct's
// `fields_excluding_tail` holds the last field.
#[thrust_macros::requires(forall(|i: usize, d: &&LayoutData, n: Niche|
    !(i + 1 < (*fields).len()
        && thrust_macros::post!(<F as Deref>::deref(&(*fields)[i]), d)
        && (**d).largest_niche == Some(n))
        || Primitive::wf_in(n.value, *dl)))]
#[thrust_macros::requires(forall(|i: usize, d: &&LayoutData, p: Primitive|
    !(i < (*fields).len()
        && thrust_macros::post!(<F as Deref>::deref(&(*fields)[i]), d)
        && (**d).backend_repr == BackendRepr::Scalar(p))
        || Primitive::wf_in(p, *dl)))]
#[thrust_macros::ensures(true)]
#[thrust_macros::context]
#[cfg(not(inferred_closures))]
fn field_closures<'a, F: Deref<Target = &'a LayoutData> + Copy + thrust_models::Model>(
    fields: &[F],
    offsets: &Vec<u64>,
    dl: &Dl,
    maybe_unsized: bool,
) -> (u64, u128, u64) {
    let end = if maybe_unsized { fields.len() - 1 } else { fields.len() };
    let fields_excluding_tail = &fields[..end];

    let max_field_align = Map::new(fields_excluding_tail.iter(), thrust_macros::closure!(
        requires(true),
        ensures(true),
        |f: &F| -> u64 { f.align },
    ))
        .max()
        .unwrap_or(1);
    let largest_niche_size = Map::new(fields_excluding_tail.iter(), thrust_macros::closure!(
        captures(dl: &mut &&Dl),
        requires(forall(|d: &&LayoutData, n: Niche|
            !(thrust_macros::post!(<F as Deref>::deref(f), d) && (**d).largest_niche == Some(n))
                || Primitive::wf_in(n.value, ***dl))),
        ensures(true),
        |f: &F| -> u128 {
            f.largest_niche.map_or(0, thrust_macros::closure!(
                captures(dl: &&&Dl),
                requires(Primitive::wf_in(n.value, ***dl)),
                ensures(true),
                |n: Niche| -> u128 { n.available(dl) },
            ))
        },
    ))
    .max()
    .unwrap_or(0);

    let mut pair = 0;
    let mut non_zst_fields = Filter::new(iter_enumerated(fields), thrust_macros::closure!(
        requires(true),
        ensures(true),
        |p: &(usize, &F)| -> bool { !p.1.is_zst() },
    ));
    match (
        non_zst_fields.next(),
        non_zst_fields.next(),
        non_zst_fields.next(),
    ) {
        (Some((i, field)), None, None) => {
            pair = offsets[i];
        }
        (Some((i, a)), Some((j, b)), None) => match (a.backend_repr, b.backend_repr) {
            (BackendRepr::Scalar(a), BackendRepr::Scalar(b)) => {
                // A step of `scalar_pair`'s `requires`, before the order of the pair is chosen.
                thrust_macros::proof_assert!(|a: Primitive, b: Primitive, dl: &Dl|
                    Primitive::wf_in(a, *dl) && Primitive::wf_in(b, *dl));
                let (a, b) = if offsets[i] < offsets[j] { (a, b) } else { (b, a) };
                pair = scalar_pair(dl, a, b);
            }
            _ => {}
        },
        _ => {}
    }
    (max_field_align, largest_niche_size, pair)
}

// The same with the closures' contracts inferred, under `--cfg inferred_closures`.
#[thrust_macros::requires(!maybe_unsized || (*fields).len() > 0)]
#[thrust_macros::requires((*offsets).len() == (*fields).len())]
#[thrust_macros::requires(forall(|i: usize, d: &&LayoutData, n: Niche|
    !(i < (*fields).len()
        && thrust_macros::post!(<F as Deref>::deref(&(*fields)[i]), d)
        && (**d).largest_niche == Some(n))
        || Primitive::wf_in(n.value, *dl)))]
#[thrust_macros::requires(forall(|i: usize, d: &&LayoutData, p: Primitive|
    !(i < (*fields).len()
        && thrust_macros::post!(<F as Deref>::deref(&(*fields)[i]), d)
        && (**d).backend_repr == BackendRepr::Scalar(p))
        || Primitive::wf_in(p, *dl)))]
#[thrust_macros::ensures(true)]
#[cfg(inferred_closures)]
fn field_closures<'a, F: Deref<Target = &'a LayoutData> + Copy + thrust_models::Model>(
    fields: &[F],
    offsets: &Vec<u64>,
    dl: &Dl,
    maybe_unsized: bool,
) -> (u64, u128, u64) {
    let end = if maybe_unsized { fields.len() - 1 } else { fields.len() };
    let fields_excluding_tail = &fields[..end];

    let max_field_align = Map::new(fields_excluding_tail.iter(), |f: &F| f.align)
        .max()
        .unwrap_or(1);
    let largest_niche_size = Map::new(fields_excluding_tail.iter(), |f: &F| {
        f.largest_niche.map_or(0, |n| n.available(dl))
    })
    .max()
    .unwrap_or(0);

    let mut pair = 0;
    let mut non_zst_fields = Filter::new(iter_enumerated(fields), |&(_, f): &(usize, &F)| !f.is_zst());
    match (
        non_zst_fields.next(),
        non_zst_fields.next(),
        non_zst_fields.next(),
    ) {
        (Some((i, field)), None, None) => {
            pair = offsets[i];
        }
        (Some((i, a)), Some((j, b)), None) => match (a.backend_repr, b.backend_repr) {
            (BackendRepr::Scalar(a), BackendRepr::Scalar(b)) => {
                let (a, b) = if offsets[i] < offsets[j] { (a, b) } else { (b, a) };
                pair = scalar_pair(dl, a, b);
            }
            _ => {}
        },
        _ => {}
    }
    (max_field_align, largest_niche_size, pair)
}

fn main() {}

//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:804d76744 THRUST_TRY_SPECS=1

// The enumerate position over a bit-set iterator stays below the domain size: `BitIter`'s model
// is (bound, count), as in tests/ui/pass/rustc_coroutine/eligibility.rs.

use thrust_models::model::{Int, Mut, Seq};
use thrust_models::{exists, forall};

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

    // Creusot's `enumerate` (creusot-std/src/std/iter.rs) without its two requirements, which are
    // there only for the absence of overflow in the count (Thrust's integers do not wrap).
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(result.0 == self && result.1 == 0)]
    fn enumerate(self) -> Enumerate<Self>
    where
        Self: Sized,
        <Self as thrust_models::Model>::Ty: PartialEq,
    {
        Enumerate { iter: self, count: 0 }
    }
}

// Creusot's `Enumerate` (creusot-std/src/std/iter/enumerate.rs): the inner iterator and the
// number of items yielded so far.
pub struct Enumerate<I> {
    iter: I,
    count: usize,
}

impl<I: thrust_models::Model> thrust_models::Model for Enumerate<I> {
    type Ty = (<I as thrust_models::Model>::Ty, Int);
}

#[thrust_macros::context]
impl<I> Iterator for Enumerate<I>
where
    I: Iterator,
    I::Item: thrust_models::Model,
    <I::Item as thrust_models::Model>::Ty: PartialEq,
    <I as thrust_models::Model>::Ty: PartialEq,
{
    type Item = (usize, I::Item);

    fn next(&mut self) -> Option<(usize, I::Item)> {
        match self.iter.next() {
            None => None,
            Some(x) => {
                let n = self.count;
                self.count += 1;
                Some((n, x))
            }
        }
    }

    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        I::invariant(self.0)
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as thrust_models::Model>::Ty>, o: Self) -> bool {
        visited.len() == o.1 - self.1
            && exists(|s: Seq<<I::Item as thrust_models::Model>::Ty>|
                I::produces(self.0, s, o.0)
                    && s.len() == visited.len()
                    && forall(|i: Int| !(0 <= i && i < s.len()) || visited[i] == (self.1 + i, s[i])))
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        I::completed(Mut::new((*self).0, (!self).0)) && (*self).1 == (!self).1
    }
}

pub struct DenseBitSet {
    domain_size: usize,
    marker: (),
}

impl thrust_models::Model for DenseBitSet {
    type Ty = (Int, ());
}

pub struct BitIter {}

impl thrust_models::Model for BitIter {
    type Ty = (Int, Int);
}

#[thrust_macros::context]
impl DenseBitSet {
    #[thrust::trusted]
    #[thrust_macros::ensures(result.0 == domain_size)]
    fn new_empty(domain_size: usize) -> DenseBitSet {
        DenseBitSet { domain_size, marker: () }
    }

    #[thrust::trusted]
    #[thrust::callable]
    #[thrust_macros::ensures(result.0 == (*self).0 && result.1 == 0)]
    fn iter(&self) -> BitIter {
        BitIter {}
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
        0 <= self.1 && self.1 <= self.0
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as thrust_models::Model>::Ty>, o: Self) -> bool {
        self.0 == o.0
            && o.1 == self.1 + visited.len()
            && o.1 <= self.0
            && forall(|i: Int| !(0 <= i && i < visited.len()) || visited[i] < self.0)
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        true
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

#[thrust_macros::requires(idx < n)]
#[thrust_macros::ensures(true)]
fn need(idx: usize, n: usize) {}

fn test(n: usize) {
    let set: DenseBitSet = DenseBitSet::new_empty(n);
    let mut it = set.iter().enumerate();
    while let Some((idx, _local)) = it.next() {
        thrust_macros::invariant!(|it: Enumerate<BitIter>, n: usize|
            it.0.0 == n && it.1 == it.0.1 && 0 <= it.1 && it.1 <= n);
        need(idx, n);
    }
}

fn main() {
    test(5);
}

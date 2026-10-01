//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300 COAR_IMAGE=coar:804d76744
use thrust_models::model::{Int, Mut, Seq};
use thrust_models::{exists, forall, Model};

// Creusot's `examples/extend`: `v1.extend(v2.into_iter())` appends `v2` to `v1`. The iterator is
// std's `vec::IntoIter<u32>` under its std.rs model `(sequence, cursor)`, and `Extend` is a local
// trait whose generic `extend` is used at `I = vec::IntoIter<u32>`. Creusot's `concat` is written
// index by index.

// Creusot's `common.rs`, the iterator specification every case shares: the trait predicates
// `produces(self, visited, o)`, `completed` and `invariant` (`true` unless the impl says otherwise),
// the laws `produces_refl` and `produces_trans` in Creusot's concatenation form, which every impl
// inherits and Thrust checks at each impl (Creusot restates them per impl with empty bodies), and
// `next` with Creusot's contract.
#[thrust_macros::context]
trait Iterator
where
    Self: Model,
    Self::Item: Model,
{
    type Item;

    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, o: Self) -> bool;

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
    fn produces_trans(a: &Self, ab: Seq<<Self::Item as Model>::Ty>, b: &Self, bc: Seq<<Self::Item as Model>::Ty>, c: &Self) {}

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

// `vec::IntoIter<u32>` as an iterator of the local spec; `next` is std's, through its extern spec.
#[thrust_macros::context]
impl Iterator for std::vec::IntoIter<u32> {
    type Item = u32;

    fn next(&mut self) -> Option<u32> {
        std::iter::Iterator::next(self)
    }



    // Not `self.1 <= self.0.len()`: the Vec model does not know `len() >= 0`.
    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        0 <= self.1
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        *self == !self && (*self).1 >= (*self).0.len()
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, o: Self) -> bool {
        self.0 == o.0
            && self.1 <= o.1
            && (!(visited.len() > 0) || o.1 <= o.0.len())
            && visited.len() == o.1 - self.1
            && forall(|k: Int| !(0 <= k && k < visited.len()) || visited[k] == self.0[self.1 + k])
    }
}

// `Extend<A>` reduced to `extend` over `&mut I` (the same shape as `from_iter` in
// `traits/collect_visited_seq_i64.rs`): `self` ends as its entry value followed by what `iter`
// produced before it was completed.
#[thrust_macros::context]
trait Extend<A: Model>: Sized
where
    Self: Model<Ty = Seq<<A as Model>::Ty>>,
    <A as Model>::Ty: Model<Ty = <A as Model>::Ty>,
{
    #[thrust_macros::requires(I::invariant(*iter))]
    #[thrust_macros::ensures(exists(|pre: <I as Model>::Ty| exists(|s: Seq<<A as Model>::Ty>|
        I::produces(*iter, s, pre) && I::completed(Mut::new(pre, !iter))
            && (!self).len() == (*self).len() + s.len()
            && forall(|k: Int| 0 <= k && k < (*self).len() ==> (!self)[k] == (*self)[k])
            && forall(|k: Int| 0 <= k && k < s.len() ==> (!self)[(*self).len() + k] == s[k]))))]
    fn extend<I: Iterator<Item = A> + Model>(&mut self, iter: &mut I)
    where
        <I as Model>::Ty: Model<Ty = <I as Model>::Ty> + PartialEq;
}

#[thrust_macros::context]
impl Extend<u32> for Vec<u32> {
    fn extend<I: Iterator<Item = u32> + Model>(&mut self, iter: &mut I)
    where
        <I as Model>::Ty: Model<Ty = <I as Model>::Ty> + PartialEq,
    {
        let it = iter;
        let v = self;
        I::produces_refl(it);
        // `pushed` records what `it` produced, so the invariant needs no existential sequence.
        let mut pushed: Vec<u32> = Vec::new();
        while let Some(x) = it.next() {
            thrust_macros::invariant!(
                |it: &mut I, v: &mut Vec<u32>, pushed: Vec<u32>, iter: thrust_models::FnParam<&mut I>, self: thrust_models::FnParam<&mut Vec<u32>>|
                !it == !iter.at_entry()
                    && !v == !self.at_entry()
                    && I::invariant(*it)
                    && I::produces(*iter.at_entry(), pushed, *it)
                    && (*v).len() == (*self.at_entry()).len() + pushed.len()
                    && forall(|k: Int| 0 <= k && k < (*self.at_entry()).len() ==> (*v)[k] == (*self.at_entry())[k])
                    && forall(|k: Int| 0 <= k && k < pushed.len() ==> (*v)[(*self.at_entry()).len() + k] == pushed[k])
            );
            v.push(x);
            pushed.push(x);
        }
    }
}

// Creusot: `proof_assert! { (@v1).ext_eq((@oldv1).concat(@oldv2)) }`, with `v1` returned.
#[thrust_macros::ensures(
    result.len() == v1.len() + v2.len()
        && forall(|k: Int| 0 <= k && k < v1.len() ==> result[k] == v1[k])
        && forall(|k: Int| 0 <= k && k < v2.len() ==> result[v1.len() + k] == v2[k])
)]
fn extend_index(mut v1: Vec<u32>, v2: Vec<u32>) -> Vec<u32> {
    let mut it = v2.into_iter();
    // `v1.extend(..)` is ambiguous with std's `Extend`, which stays in scope.
    <Vec<u32> as Extend<u32>>::extend(&mut v1, &mut it);
    v1
}

fn main() {}

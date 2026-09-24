//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60 COAR_IMAGE=coar:develop-3d34b93de
use thrust_models::model::{Int, Mut, Seq};
use thrust_models::{exists, forall, Model};

// Creusot's `examples/extend`: `v1.extend(v2.into_iter())` appends `v2` to `v1`. The iterator
// spec is Creusot's `produces` form (`traits/collect_visited_seq_i64.rs`); the iterator is std's
// `vec::IntoIter<i64>` under its std.rs model `(sequence, cursor)`, and `Extend` is a local trait
// whose generic `extend` is used at `I = vec::IntoIter<i64>`. Creusot's `concat` is written
// index by index.
#[thrust_macros::context]
trait Iterator
where
    Self: Model,
    Self::Item: Model,
    <Self as Model>::Ty: Model<Ty = <Self as Model>::Ty>,
    <Self::Item as Model>::Ty: Model<Ty = <Self::Item as Model>::Ty>,
{
    type Item;

    #[thrust_macros::requires(Self::invariant(*self))]
    #[thrust_macros::ensures(Self::invariant(!self))]
    #[thrust_macros::ensures(result == None ==> Self::completed(self))]
    // `produces_trans` with a singleton second leg, applied at every `next` instead of called.
    #[thrust_macros::ensures(forall(|i| forall(|s: Seq<<Self::Item as Model>::Ty>|
        result == Some(i) && s == Seq::singleton(i) ==> Self::produces(*self, s, !self))))]
    #[thrust_macros::ensures(forall(|a: <Self as Model>::Ty| forall(|s: Seq<<Self::Item as Model>::Ty>| forall(|i| forall(|t: Seq<<Self::Item as Model>::Ty>|
        result == Some(i) && Self::produces(a, s, *self) && t == s.push(i) ==> Self::produces(a, t, !self))))))]
    fn next(&mut self) -> Option<Self::Item>;

    // Reflexivity lemma: the base case of a loop invariant `iter_old.produces(v, iter)`.
    #[thrust_macros::ensures(forall(|s: Seq<<Self::Item as Model>::Ty>| s.len() == 0 ==> Self::produces(*a, s, *a)))]
    fn produces_refl(a: &Self);

    #[thrust_macros::predicate]
    fn invariant(self) -> bool;
    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool;
    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, o: Self) -> bool;
}

// `vec::IntoIter<i64>` as an iterator of the local spec; `next` is std's, through its extern spec.
#[thrust_macros::context]
impl Iterator for std::vec::IntoIter<i64> {
    type Item = i64;

    fn next(&mut self) -> Option<i64> {
        std::iter::Iterator::next(self)
    }

    fn produces_refl(a: &std::vec::IntoIter<i64>) {}

    // 0 <= self.1 (not `self.1 <= self.0.len()`: the Vec model does not know `len() >= 0`)
    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        "(<= 0 (tuple_proj<Seq<Int>-Int>.1 self_))";
        true
    }

    // self.resolve() && self.1 >= self.0.len()
    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        "(and
            (= (mut_current<Tuple<Seq<Int>-Int>> self_) (mut_final<Tuple<Seq<Int>-Int>> self_))
            (>= (tuple_proj<Seq<Int>-Int>.1 (mut_current<Tuple<Seq<Int>-Int>> self_))
                (seq.len (tuple_proj<Seq<Int>-Int>.0 (mut_current<Tuple<Seq<Int>-Int>> self_)))))";
        true
    }

    // self.0 == o.0 && self.1 <= o.1 && (visited.len() > 0 ==> o.1 <= o.0.len())
    // && visited.len() == o.1 - self.1
    // && forall k. 0 <= k < visited.len() ==> visited[k] == self.0[self.1 + k]
    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, o: Self) -> bool {
        "(and
            (= (tuple_proj<Seq<Int>-Int>.0 self_) (tuple_proj<Seq<Int>-Int>.0 o))
            (<= (tuple_proj<Seq<Int>-Int>.1 self_) (tuple_proj<Seq<Int>-Int>.1 o))
            (=> (> (seq.len visited) 0)
                (<= (tuple_proj<Seq<Int>-Int>.1 o)
                    (seq.len (tuple_proj<Seq<Int>-Int>.0 o))))
            (= (seq.len visited)
               (- (tuple_proj<Seq<Int>-Int>.1 o) (tuple_proj<Seq<Int>-Int>.1 self_)))
            (forall ((zk Int))
                (=> (and (<= 0 zk) (< zk (seq.len visited)))
                    (= (seq.nth visited zk)
                       (seq.nth (tuple_proj<Seq<Int>-Int>.0 self_)
                               (+ (tuple_proj<Seq<Int>-Int>.1 self_) zk))))))";
        true
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
impl Extend<i64> for Vec<i64> {
    fn extend<I: Iterator<Item = i64> + Model>(&mut self, iter: &mut I)
    where
        <I as Model>::Ty: Model<Ty = <I as Model>::Ty> + PartialEq,
    {
        let it = iter;
        let v = self;
        I::produces_refl(it);
        // `pushed` records what `it` produced, so the invariant needs no existential sequence.
        let mut pushed: Vec<i64> = Vec::new();
        while let Some(x) = it.next() {
            thrust_macros::invariant!(
                |it: &mut I, v: &mut Vec<i64>, pushed: Vec<i64>, iter: thrust_models::FnParam<&mut I>, self: thrust_models::FnParam<&mut Vec<i64>>|
                !it == !iter.at_entry()
                    && !v == !self.at_entry()
                    && I::invariant(*it)
                    && I::produces(*iter.at_entry(), pushed, *it)
                    && pushed.len() >= 0
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
// The Vec model does not know `len() >= 0`; the requires supplies it, as in `iterators/`.
#[thrust_macros::requires(v2.len() >= 0)]
#[thrust_macros::ensures(
    result.len() == v1.len() + v2.len() + 1
        && forall(|k: Int| 0 <= k && k < v1.len() ==> result[k] == v1[k])
        && forall(|k: Int| 0 <= k && k < v2.len() ==> result[v1.len() + k] == v2[k])
)]
fn extend_index(mut v1: Vec<i64>, v2: Vec<i64>) -> Vec<i64> {
    let mut it = v2.into_iter();
    // `v1.extend(..)` is ambiguous with std's `Extend`, which stays in scope.
    <Vec<i64> as Extend<i64>>::extend(&mut v1, &mut it);
    v1
}

fn main() {}

//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables
use thrust_models::{exists, forall, Model};
use thrust_models::model::{Int, Mut, Seq};

// Creusot's `examples/skip_take`: `iter.take(n).skip(n).next()` is `None` for any iterator. The
// trait follows Creusot's `common.rs`: `produces_refl` (guarded by the invariant) and
// `produces_trans` are `#[law]`s, and `next` ensures only `completed` on `None` and the one-step
// `produces` on `Some`. `Take` is Creusot's `take.rs`; `Skip` is `traits/skip.rs` with Creusot's
// concatenated `produces`, stacked as `Skip<Take<I>>` and used at a generic `I`.
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
    #[thrust_macros::ensures(forall(|i| result == Some(i) ==> Self::produces(*self, Seq::singleton(i), !self)))]
    #[thrust_macros::ensures(forall(|a: <Self as Model>::Ty| forall(|s: Seq<<Self::Item as Model>::Ty>| forall(|i|
        result == Some(i) && Self::produces(a, s, *self) ==> Self::produces(a, s.push(i), !self)))))]
    fn next(&mut self) -> Option<Self::Item>;

    // Reflexivity is supplied only by this law, guarded by the invariant as in Creusot's
    // `common.rs`; `next` does not ensure it. Callable where a loop invariant needs its base case
    // (`Skip::next`'s entry).
    #[thrust_macros::law]
    #[thrust_macros::requires(Self::invariant(*a))]
    #[thrust_macros::ensures(Self::produces(*a, Seq::empty(), *a))]
    fn produces_refl(a: &Self);

    // Creusot's `produces_trans` in its concatenation form, as a law.
    #[thrust_macros::law]
    #[thrust_macros::requires(Self::produces(*a, ab, *b) && Self::produces(*b, bc, *c))]
    #[thrust_macros::ensures(Self::produces(*a, ab.concat(bc), *c))]
    fn produces_trans(a: &Self, ab: Seq<<Self::Item as Model>::Ty>, b: &Self, bc: Seq<<Self::Item as Model>::Ty>, c: &Self);

    #[thrust_macros::predicate]
    fn invariant(self) -> bool;
    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool;
    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, o: Self) -> bool;
}

#[derive(PartialEq)]
pub struct Take<I> {
    iter: I,
    n: usize,
}

impl<I: Model> Model for Take<I> {
    type Ty = Take<<I as Model>::Ty>;
}

#[thrust_macros::context]
impl<I> Iterator for Take<I>
where
    I: Iterator + Model,
    <I as Iterator>::Item: Model,
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty> + PartialEq,
    <<I as Iterator>::Item as Model>::Ty: Model<Ty = <<I as Iterator>::Item as Model>::Ty> + PartialEq,
    <Take<I> as Model>::Ty: Model<Ty = <Take<I> as Model>::Ty>,
{
    type Item = I::Item;

    fn next(&mut self) -> Option<I::Item> {
        if self.n != 0 {
            self.n -= 1;
            self.iter.next()
        } else {
            None
        }
    }

    fn produces_refl(a: &Take<I>) {}

    fn produces_trans(a: &Take<I>, ab: Seq<<Self::Item as Model>::Ty>, b: &Take<I>, bc: Seq<<Self::Item as Model>::Ty>, c: &Take<I>) {}

    // self.iter.invariant() && self.n >= 0
    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        I::invariant(self.iter) && self.n >= 0
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        ((*self).n == 0 && *self == !self)
            || ((*self).n > 0
                && (*self).n == (!self).n + 1
                && I::completed(Mut::new((*self).iter, (!self).iter)))
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, o: Self) -> bool {
        self.n == o.n + visited.len() && I::produces(self.iter, visited, o.iter)
    }
}

pub struct Skip<I> {
    iter: I,
    n: usize,
}

impl<I: Model> Model for Skip<I> {
    type Ty = (<I as Model>::Ty, Int);
}

#[thrust_macros::context]
impl<I> Iterator for Skip<I>
where
    I: Iterator + Model,
    <I as Iterator>::Item: Model,
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty> + PartialEq,
    <<I as Iterator>::Item as Model>::Ty: Model<Ty = <<I as Iterator>::Item as Model>::Ty> + PartialEq,
    <Skip<I> as Model>::Ty: Model<Ty = <Skip<I> as Model>::Ty>,
{
    type Item = I::Item;

    fn next(&mut self) -> Option<I::Item> {
        let s = self;
        let mut n = s.n;
        s.n = 0;
        I::produces_refl(&s.iter);
        loop {
            // Creusot's four invariants: proph_const, produces (the skipped prefix), n_0, inv;
            // plus `n` bounded, and "no iteration yet => the inner iterator is untouched".
            thrust_macros::invariant!(
                |s: &mut Skip<I>, n: usize, self: thrust_models::FnParam<&mut Skip<I>>|
                    !s == !self.at_entry()
                        && (*s).1 == 0
                        && I::invariant((*s).0)
                        && 0 <= n
                        && n <= (*self.at_entry()).1
                        && (n == (*self.at_entry()).1 ==> (*s).0 == (*self.at_entry()).0)
                        && exists(|t: Seq<<<I as Iterator>::Item as Model>::Ty>|
                            t.len() + n == (*self.at_entry()).1
                                && I::produces((*self.at_entry()).0, t, (*s).0))
            );
            let r = s.iter.next();
            if n == 0 {
                return r;
            }
            match r {
                None => return None,
                Some(_) => {}
            }
            n -= 1;
        }
    }

    fn produces_refl(a: &Skip<I>) {}

    fn produces_trans(a: &Skip<I>, ab: Seq<<Self::Item as Model>::Ty>, b: &Skip<I>, bc: Seq<<Self::Item as Model>::Ty>, c: &Skip<I>) {}

    // self.iter.invariant() && self.n >= 0
    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        I::invariant(self.0) && self.1 >= 0
    }

    // (!self).n == 0
    // && exists s j. s.len() <= (*self).n && (*self).iter.produces(s, j) && I::completed(Mut::new(j, (!self).iter))
    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        (!self).1 == 0
            && exists(|s: Seq<<Self::Item as Model>::Ty>| exists(|j: <I as Model>::Ty|
                s.len() <= (*self).1
                    && I::produces((*self).0, s, j)
                    && I::completed(Mut::new(j, (!self).0))))
    }

    // (visited.len() == 0 && self == o)
    // or (o.n == 0 && visited.len() > 0 && exists s. s.len() == self.n
    //     && self.iter.produces(s.concat(visited), o.iter))
    // Creusot's statement: the inner iterator produces the `self.n` skipped items `s`, then
    // `visited`, as one concatenated sequence.
    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, o: Self) -> bool {
        (visited.len() == 0 && self == o)
            || (o.1 == 0
                && visited.len() > 0
                && exists(|s: Seq<<Self::Item as Model>::Ty>|
                    s.len() == self.1
                        && I::produces(self.0, s.concat(visited), o.0)))
    }
}

#[derive(PartialEq)]
struct Range {
    start: i64,
    end: i64,
}

impl Model for Range {
    type Ty = Range;
}

#[thrust_macros::context]
impl Iterator for Range {
    type Item = i64;

    fn next(&mut self) -> Option<Self::Item> {
        if self.start < self.end {
            let item = self.start;
            self.start += 1;
            Some(item)
        } else {
            None
        }
    }

    fn produces_refl(a: &Range) {}

    fn produces_trans(a: &Range, ab: Seq<<Self::Item as Model>::Ty>, b: &Range, bc: Seq<<Self::Item as Model>::Ty>, c: &Range) {}

    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        true
    }

    // self.resolve() && self.start >= self.end
    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        *self == !self && (*self).start >= (*self).end
    }

    // self.end == o.end && self.start <= o.start
    // && (visited.len() > 0 ==> o.start <= o.end)
    // && visited.len() == o.start - self.start
    // && forall i. 0 <= i < visited.len() ==> visited[i] == self.start + i
    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, o: Self) -> bool {
        self.end == o.end
            && self.start <= o.start
            && (!(visited.len() > 0) || o.start <= o.end)
            && visited.len() == o.start - self.start
            && forall(|i: Int| !(0 <= i && i < visited.len()) || visited[i] == self.start + i)
    }
}

// Creusot: `#[requires(iter.invariant())] fn skip_take<I: Iterator>(iter: I, n: usize)` with
// `proof_assert! { res == None }`.
#[thrust_macros::context]
#[thrust_macros::requires(I::invariant(iter))]
fn skip_take<I>(iter: I, n: usize)
where
    I: Iterator + Model,
    <I as Iterator>::Item: Model,
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty> + PartialEq,
    <<I as Iterator>::Item as Model>::Ty: Model<Ty = <<I as Iterator>::Item as Model>::Ty> + PartialEq,
{
    let mut s = Skip { iter: Take { iter, n }, n };
    let res = s.next();
    assert!(matches!(res, None));
}

fn main() {
    skip_take(Range { start: 0, end: 10 }, 3);
}

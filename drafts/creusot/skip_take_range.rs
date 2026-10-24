//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60 COAR_IMAGE=coar:develop-3d34b93de
use thrust_models::model::{Int, Mut, Seq};
use thrust_models::{exists, forall, Model};

// Creusot's `examples/skip_take`: `iter.take(n).skip(n).next()` is `None` for any iterator.
// `Take` is `creusot/take.rs`'s and `Skip` is `creusot/skip.rs`'s, stacked as `Skip<Take<Range>>`. `skip_take.rs` is the same call site at a
// generic `I`, as Creusot writes it.

// Creusot's `common.rs`, the iterator specification every case shares: the trait predicates
// `produces(self, visited, o)`, `completed` and `invariant` (`true` unless the impl says otherwise),
// the laws `produces_refl` and `produces_trans` in Creusot's concatenation form, proved by each
// impl, and `next` with Creusot's contract.
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
    fn produces_refl(a: &Self);

    #[thrust_macros::law]
    #[thrust_macros::requires(Self::produces(*a, ab, *b))]
    #[thrust_macros::requires(Self::produces(*b, bc, *c))]
    #[thrust_macros::ensures(Self::produces(*a, ab.concat(bc), *c))]
    fn produces_trans(a: &Self, ab: Seq<<Self::Item as Model>::Ty>, b: &Self, bc: Seq<<Self::Item as Model>::Ty>, c: &Self);

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

pub struct Take<I> {
    iter: I,
    n: usize,
}

impl<I: Model> Model for Take<I> {
    type Ty = (<I as Model>::Ty, Int);
}

#[thrust_macros::context]
impl<I> Iterator for Take<I>
where
    I: Iterator + Model,
    <I as Iterator>::Item: Model,
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty> + PartialEq,
    <<I as Iterator>::Item as Model>::Ty: Model<Ty = <<I as Iterator>::Item as Model>::Ty>,
    <Take<I> as Model>::Ty: Model<Ty = <Take<I> as Model>::Ty>,
{
    type Item = I::Item;

    fn next(&mut self) -> Option<I::Item> {
        if self.n != 0 {
            self.n -= 1;
            self.iter.next()
        } else {
            I::produces_refl(&self.iter);
            None
        }
    }

    fn produces_refl(a: &Take<I>) {}

    fn produces_trans(a: &Take<I>, ab: Seq<<Self::Item as Model>::Ty>, b: &Take<I>, bc: Seq<<Self::Item as Model>::Ty>, c: &Take<I>) {}

    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        I::invariant(self.0) && self.1 >= 0
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        ((*self).1 == 0 && *self == !self)
            || ((*self).1 > 0
                && (*self).1 == (!self).1 + 1
                && I::completed(Mut::new((*self).0, (!self).0)))
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, o: Self) -> bool {
        self.1 == o.1 + visited.len() && I::produces(self.0, visited, o.0)
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

    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        I::invariant(self.0) && self.1 >= 0
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        (!self).1 == 0
            && exists(|s: Seq<<Self::Item as Model>::Ty>| exists(|j: <I as Model>::Ty|
                s.len() <= (*self).1
                    && I::produces((*self).0, s, j)
                    && I::completed(Mut::new(j, (!self).0))))
    }

    // `t` is Creusot's `s.concat(visited)` with `s.len() == self.n`, written without `concat`.
    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, o: Self) -> bool {
        (visited.len() == 0 && self == o)
            || (o.1 == 0
                && visited.len() > 0
                && exists(|t: Seq<<Self::Item as Model>::Ty>|
                    t.len() == self.1 + visited.len()
                        && forall(|k: Int| !(self.1 <= k && k < t.len()) || t[k] == visited[k - self.1])
                        && I::produces(self.0, t, o.0)))
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

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        *self == !self && (*self).start >= (*self).end
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, o: Self) -> bool {
        self.end == o.end
            && self.start <= o.start
            && (!(visited.len() > 0) || o.start <= o.end)
            && visited.len() == o.start - self.start
            && forall(|i: Int| !(0 <= i && i < visited.len()) || visited[i] == self.start + i)
    }
}

// Creusot's call site with the generic `I` replaced by `Range`.
fn skip_take_range(start: i64, end: i64, n: usize) {
    let mut s = Skip { iter: Take { iter: Range { start, end }, n }, n };
    let res = s.next();
    assert!(matches!(res, None));
}

fn main() {}

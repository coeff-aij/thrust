//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120 COAR_IMAGE=coar:develop-2493045c3
use thrust_models::model::{Int, Mut, Seq};
use thrust_models::{exists, forall, Model};

// Creusot's `common.rs` iterator spec: ternary `produces(self, visited, o)`, `completed`, and the
// laws applied as ensures on `next`; reflexivity is also a callable law (`produces_refl`).
// The generic `Skip` follows Creusot's `skip.rs`: `next` drains up to `n` items in a loop whose
// invariant carries the skipped prefix, then answers with the inner iterator's result.
// `skip_step.rs` is the same adapter in the step form of the iterator spec.
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
    #[thrust_macros::ensures(Self::produces(*self, Seq::empty(), *self))]
    #[thrust_macros::ensures(forall(|i| result == Some(i) ==> Self::produces(*self, Seq::singleton(i), !self)))]
    #[thrust_macros::ensures(forall(|a: <Self as Model>::Ty| forall(|s: Seq<<Self::Item as Model>::Ty>| forall(|i|
        result == Some(i) && Self::produces(a, s, *self) ==> Self::produces(a, s.push(i), !self)))))]
    fn next(&mut self) -> Option<Self::Item>;

    // Reflexivity as a callable law: the base case of a loop invariant `old.produces(t, cur)`.
    #[thrust_macros::ensures(Self::produces(*a, Seq::empty(), *a))]
    fn produces_refl(a: &Self);

    #[thrust_macros::predicate]
    fn invariant(self) -> bool;
    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool;
    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, o: Self) -> bool;
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
                    s.len() == self.1 + 1
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

fn main() {}

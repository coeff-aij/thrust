//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60 COAR_IMAGE=coar:develop-3d34b93de
use thrust_models::model::{Int, Seq};
use thrust_models::{exists, forall, Model};

// Creusot's `examples/skip_take`: `iter.take(n).skip(n).next()` is `None` for any iterator.
// The iterator spec is Creusot's `produces` form; `Take` is `traits/take.rs`'s and `Skip` is
// `traits/skip.rs`'s, stacked as `Skip<Take<I>>` and used at a generic `I`.
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
    #[thrust_macros::ensures(forall(|s: Seq<<Self::Item as Model>::Ty>| s.len() == 0 ==> Self::produces(*self, s, *self)))]
    #[thrust_macros::ensures(forall(|i| forall(|s: Seq<<Self::Item as Model>::Ty>|
        result == Some(i) && s.len() == 1 && s[0] == i ==> Self::produces(*self, s, !self))))]
    #[thrust_macros::ensures(forall(|a: <Self as Model>::Ty| forall(|s: Seq<<Self::Item as Model>::Ty>| forall(|i| forall(|t: Seq<<Self::Item as Model>::Ty>|
        result == Some(i) && Self::produces(a, s, *self) && t == s.push(i) ==> Self::produces(a, t, !self))))))]
    fn next(&mut self) -> Option<Self::Item>;

    // Reflexivity as a callable law: the base case of a loop invariant `old.produces(t, cur)`.
    #[thrust_macros::ensures(forall(|s: Seq<<Self::Item as Model>::Ty>| s.len() == 0 ==> Self::produces(*a, s, *a)))]
    fn produces_refl(a: &Self);

    #[thrust_macros::predicate]
    fn invariant(self) -> bool;
    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool;
    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, o: Self) -> bool;
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

    fn produces_refl(a: &Take<I>) {
        I::produces_refl(&a.iter);
    }

    // self.iter.invariant() && self.n >= 0
    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        "(and
            (q_invariant_10af08a4745b9eef414e2500cf19a50d<a0> (tuple_proj<a0-Int>.0 self_))
            (>= (tuple_proj<a0-Int>.1 self_) 0)
        )";
        true
    }

    // (*self.n == 0 && *self == !self) ||
    // (*self.n > 0 && *self.n == !self.n + 1 && self.iter.completed())
    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        "(or
            (and
                (= (tuple_proj<a0-Int>.1 (mut_current<Tuple<a0-Int>> self_)) 0)
                (= (mut_current<Tuple<a0-Int>> self_) (mut_final<Tuple<a0-Int>> self_)))
            (and
                (> (tuple_proj<a0-Int>.1 (mut_current<Tuple<a0-Int>> self_)) 0)
                (= (tuple_proj<a0-Int>.1 (mut_current<Tuple<a0-Int>> self_))
                   (+ (tuple_proj<a0-Int>.1 (mut_final<Tuple<a0-Int>> self_)) 1))
                (q_completed_10af08a4745b9eefca83dae4428a001<a0>
                    (mut<a0>
                        (tuple_proj<a0-Int>.0 (mut_current<Tuple<a0-Int>> self_))
                        (tuple_proj<a0-Int>.0 (mut_final<Tuple<a0-Int>> self_))))))";
        true
    }

    // self.n == o.n + visited.len() && self.iter.produces(visited, o.iter)
    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, o: Self) -> bool {
        "(and
            (= (tuple_proj<a0-Int>.1 self_)
               (+ (tuple_proj<a0-Int>.1 o) (tuple_proj<Array<Int-a1>-Int>.1 visited)))
            (q_produces_10af08a4745b9eefba239aa8dc77de31<a0> (tuple_proj<a0-Int>.0 self_) visited (tuple_proj<a0-Int>.0 o)))";
        true
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

    // self.iter.invariant() && self.n >= 0
    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        "(and
            (q_invariant_10af08a4745b9eef414e2500cf19a50d<a2> (tuple_proj<a2-Int>.0 self_))
            (>= (tuple_proj<a2-Int>.1 self_) 0))";
        true
    }

    // (!self).n == 0
    // && exists s j. s.len() <= (*self).n && (*self).iter.produces(s, j) && I::completed(Mut::new(j, (!self).iter))
    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        "(and
            (= (tuple_proj<a2-Int>.1 (mut_final<Tuple<a2-Int>> self_)) 0)
            (exists ((sa (Array Int a3)) (sl Int) (zj a2))
                (and
                    (<= 0 sl)
                    (<= sl (tuple_proj<a2-Int>.1 (mut_current<Tuple<a2-Int>> self_)))
                    (q_produces_10af08a4745b9eefba239aa8dc77de31<a2>
                        (tuple_proj<a2-Int>.0 (mut_current<Tuple<a2-Int>> self_))
                        (tuple<Array<Int-a3>-Int> sa sl)
                        zj)
                    (q_completed_10af08a4745b9eefca83dae4428a001<a2>
                        (mut<a2> zj (tuple_proj<a2-Int>.0 (mut_final<Tuple<a2-Int>> self_)))))))";
        true
    }

    // (visited.len() == 0 && self == o)
    // or (o.n == 0 && visited.len() > 0 && exists t. t.len() == self.n + visited.len()
    //     && (forall k. self.n <= k < t.len() ==> t[k] == visited[k - self.n])
    //     && self.iter.produces(t, o.iter))
    // `t` is Creusot's `s.concat(visited)` with `s.len() == self.n`, written without `concat`.
    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, o: Self) -> bool {
        "(or
            (and
                (= (tuple_proj<Array<Int-a3>-Int>.1 visited) 0)
                (= self_ o))
            (and
                (= (tuple_proj<a2-Int>.1 o) 0)
                (> (tuple_proj<Array<Int-a3>-Int>.1 visited) 0)
                (exists ((ta (Array Int a3)) (tl Int))
                    (and
                        (= tl (+ (tuple_proj<a2-Int>.1 self_) (tuple_proj<Array<Int-a3>-Int>.1 visited)))
                        (forall ((zk Int))
                            (=> (and (<= (tuple_proj<a2-Int>.1 self_) zk) (< zk tl))
                                (= (select ta zk)
                                   (select (tuple_proj<Array<Int-a3>-Int>.0 visited)
                                           (- zk (tuple_proj<a2-Int>.1 self_))))))
                        (q_produces_10af08a4745b9eefba239aa8dc77de31<a2> (tuple_proj<a2-Int>.0 self_) (tuple<Array<Int-a3>-Int> ta tl) (tuple_proj<a2-Int>.0 o))))))";
        true
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
        "true";
        true
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        // self.resolve() && self.start >= self.end
        "(and
            (= (mut_current<Tuple<Int-Int>> self_) (mut_final<Tuple<Int-Int>> self_))
            (>= (tuple_proj<Int-Int>.0 (mut_current<Tuple<Int-Int>> self_))
                (tuple_proj<Int-Int>.1 (mut_current<Tuple<Int-Int>> self_)))
        )";
        true
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, o: Self) -> bool {
        // self.end == o.end && self.start <= o.start
        // && (visited.len() > 0 ==> o.start <= o.end)
        // && visited.len() == o.start - self.start
        // && forall i. 0 <= i < visited.len() ==> visited[i] == self.start + i
        "(and
            (= (tuple_proj<Int-Int>.1 self_) (tuple_proj<Int-Int>.1 o))
            (<= (tuple_proj<Int-Int>.0 self_) (tuple_proj<Int-Int>.0 o))
            (=> (> (tuple_proj<Array<Int-Int>-Int>.1 visited) 0)
                (<= (tuple_proj<Int-Int>.0 o) (tuple_proj<Int-Int>.1 o)))
            (= (tuple_proj<Array<Int-Int>-Int>.1 visited)
               (- (tuple_proj<Int-Int>.0 o) (tuple_proj<Int-Int>.0 self_)))
            (forall ((zi Int))
                (=> (and (<= 0 zi) (< zi (tuple_proj<Array<Int-Int>-Int>.1 visited)))
                    (= (select (tuple_proj<Array<Int-Int>-Int>.0 visited) zi)
                       (+ (tuple_proj<Int-Int>.0 self_) zi))))
        )";
        true
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
    let mut s = Skip { iter: Take { iter, n: n + 1 }, n };
    let res = s.next();
    assert!(matches!(res, None));
}

fn main() {}

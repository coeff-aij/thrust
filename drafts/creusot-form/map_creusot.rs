//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120 COAR_IMAGE=coar:develop-2493045c3
use thrust_models::model::{Closure, Mut, Seq};
use thrust_models::{exists, forall, Model};

// Creusot's `Map` in Creusot's own form (the artifact's `iterators/map.rs` for an `Fn` closure):
// ternary `produces` with an existentially quantified input sequence, and the invariant made of
// `next_precondition`, `preservation` and `reinitialize`. Predicate bodies are Rust syntax and the
// trait laws are `#[law]`s, so no symbol is written by hand.
#[thrust_macros::context]
trait Iterator
where
    Self: Model,
    Self::Item: Model,
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

    // Reflexivity as a callable law: an adapter that answers without touching its inner
    // iterator (`Take` at `n == 0`) has no `next` ensures of the inner to take it from.
    #[thrust_macros::law]
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


struct Map<I, F> {
    iter: I,
    func: F,
}

impl<I: Model, F> Model for Map<I, F> {
    type Ty = Map<<I as Model>::Ty, Closure<F>>;
}

#[thrust_macros::context]
impl<I, B, F> Map<I, F>
where
    I: Iterator + Model,
    B: Model,
    F: Fn(I::Item) -> B,
    <I as Iterator>::Item: Model,
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty> + PartialEq,
    <<I as Iterator>::Item as Model>::Ty: Model<Ty = <<I as Iterator>::Item as Model>::Ty> + PartialEq,
    <B as Model>::Ty: PartialEq,
{
    // forall e i. iter.produces([e], i) ==> pre(func(e))
    #[thrust_macros::predicate]
    fn next_precondition(iter: I, func: F) -> bool {
        forall(|e: <<I as Iterator>::Item as Model>::Ty| forall(|i: <I as Model>::Ty|
            !I::produces(iter, Seq::singleton(e), i) || thrust_macros::pre!(func(e))))
    }

    // forall s e1 e2 i b. iter.produces(s.push(e1).push(e2), i) && post(func(e1), b) ==> pre(func(e2))
    #[thrust_macros::predicate]
    fn preservation(iter: I, func: F) -> bool {
        forall(|s: Seq<<<I as Iterator>::Item as Model>::Ty>|
        forall(|e1: <<I as Iterator>::Item as Model>::Ty|
        forall(|e2: <<I as Iterator>::Item as Model>::Ty|
        forall(|i: <I as Model>::Ty|
        forall(|b: <B as Model>::Ty|
            !(I::produces(iter, s.push(e1).push(e2), i) && thrust_macros::post!(func(e1), b))
                || thrust_macros::pre!(func(e2)))))))
    }

    // forall cur fin. completed(Mut(cur, fin)) ==> next_precondition(fin) && preservation(fin)
    #[thrust_macros::predicate]
    fn reinitialize(func: F) -> bool {
        forall(|cur: <I as Model>::Ty| forall(|fin: <I as Model>::Ty|
            !I::completed(Mut::new(cur, fin))
                || (Self::next_precondition(fin, func) && Self::preservation(fin, func))))
    }
}

#[thrust_macros::context]
impl<I, B, F> Iterator for Map<I, F>
where
    I: Iterator + Model,
    B: Model,
    F: Fn(I::Item) -> B,
    <I as Iterator>::Item: Model,
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty> + PartialEq,
    <<I as Iterator>::Item as Model>::Ty: Model<Ty = <<I as Iterator>::Item as Model>::Ty> + PartialEq,
    <B as Model>::Ty: Model<Ty = <B as Model>::Ty> + PartialEq,
{
    type Item = B;

    fn next(&mut self) -> Option<B> {
        match self.iter.next() {
            Some(v) => Some((self.func)(v)),
            None => None,
        }
    }

    fn produces_refl(a: &Map<I, F>) {}

    fn produces_trans(a: &Map<I, F>, ab: Seq<<Self::Item as Model>::Ty>, b: &Map<I, F>, bc: Seq<<Self::Item as Model>::Ty>, c: &Map<I, F>) {}

    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        I::invariant(self.iter)
            && Self::next_precondition(self.iter, self.func)
            && Self::preservation(self.iter, self.func)
            && Self::reinitialize(self.func)
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        I::completed(Mut::new((*self).iter, (!self).iter)) && (*self).func == (!self).func
    }

    // self.func == o.func && exists s. s.len() == visited.len() && iter.produces(s, o.iter)
    //   && forall k. 0 <= k < visited.len() ==> post(func(s[k]), visited[k])
    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, o: Self) -> bool {
        self.func == o.func
            && exists(|s: Seq<<<I as Iterator>::Item as Model>::Ty>|
                s.len() == visited.len()
                    && I::produces(self.iter, s, o.iter)
                    && forall(|k: thrust_models::model::Int|
                        !(0 <= k && k < visited.len())
                            || thrust_macros::post!((self.func)(s[k]), visited[k])))
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
            (=> (> (seq.len visited) 0)
                (<= (tuple_proj<Int-Int>.0 o) (tuple_proj<Int-Int>.1 o)))
            (= (seq.len visited)
               (- (tuple_proj<Int-Int>.0 o) (tuple_proj<Int-Int>.0 self_)))
            (forall ((zi Int))
                (=> (and (<= 0 zi) (< zi (seq.len visited)))
                    (= (seq.nth visited zi)
                       (+ (tuple_proj<Int-Int>.0 self_) zi))))
        )";
        true
    }
}

fn main() {
    let f = thrust_macros::closure!(
        requires(x < 100),
        ensures(result == x * 10),
        |x: i64| -> i64 { x * 10 }
    );
    let mut m = Map {
        iter: Range { start: 0, end: 10 },
        func: f,
    };
    let first = m.next();
    let second = m.next();
    assert!(matches!(first, Some(0)));
    assert!(matches!(second, Some(10)));
}

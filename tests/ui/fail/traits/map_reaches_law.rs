//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60 COAR_IMAGE=coar:latest
use thrust_models::forall;

#[thrust_macros::context]
trait Iterator {
    type Item;

    #[thrust_macros::requires(Self::invariant(*self))]
    #[thrust_macros::ensures(Self::invariant(!self))]
    #[thrust_macros::ensures(result == None ==> Self::completed(self))]
    #[thrust_macros::ensures(forall(|i| result == Some(i) ==> Self::step(*self, i, !self)))]
    #[thrust_macros::ensures(Self::reaches(*self, !self))]
    #[thrust_macros::ensures(forall(|m| Self::reaches(!self, m) ==> Self::reaches(*self, m)))]
    fn next(&mut self) -> Option<Self::Item>;

    #[thrust_macros::predicate]
    fn invariant(self) -> bool;
    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool;
    #[thrust_macros::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool;
    /// Reflexive-transitive closure of `step`, with the produced items forgotten.
    #[thrust_macros::predicate]
    fn reaches(self, dist: Self) -> bool;
}

// Creusot states `produces_refl` / `produces_trans` as `#[law]`s on the trait. Thrust has
// no `#[law]`, so the nearest thing is a `#[thrust::trusted]` function whose body is never
// analysed. A bare transitivity law would not reach: a trusted function's `ensures` is
// injected only at the concrete arguments of the call, while invariant preservation needs
// the fact underneath the invariant's own quantifier. Putting the quantifier INSIDE the
// law's `ensures` is what makes it reach.
#[thrust::trusted]
#[thrust_macros::context]
#[thrust_macros::ensures(I::reaches(*x, *x))]
fn reaches_refl<I: Iterator + thrust_models::Model>(x: &I)
where
    <I as thrust_models::Model>::Ty: PartialEq,
    <I as Iterator>::Item: thrust_models::Model,
    <<I as Iterator>::Item as thrust_models::Model>::Ty: PartialEq,
{
}

struct Map<I, F> {
    iter: I,
    func: F,
}

impl<I, F> thrust_models::Model for Map<I, F> {
    type Ty = Map<I, F>;
}

#[thrust_macros::context]
impl<I: Iterator<Item = i64> + thrust_models::Model, F: Fn(i64) -> i64> Iterator for Map<I, F>
where
    <I as thrust_models::Model>::Ty: PartialEq,
{
    type Item = i64;

    fn next(&mut self) -> Option<Self::Item> {
        match self.iter.next() {
            Some(v) => Some((self.func)(v)),
            None => None,
        }
    }

    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        // self.iter.invariant() &&
        // forall(|m: I, e: i64, n: I|
        //     self.iter.reaches(m) && m.step(e, n) ==> pre!(self.func(e)))
        //
        // The inner iterator is a type parameter here, so `reaches` and `step` are
        // `declare-forall-fun`s over the bare abstract sort `a0` rather than the
        // `define-fun`s the monomorphised version got, and the intermediate states
        // are bound at `a0` instead of field by field at `Int`.
        "(and
            (q_invariant_b665189a22a9bc2056ad1eadd918ea04<a0> (tuple_proj<a0-a1>.0 self_))
            (forall ((zm a0) (ze Int) (zn a0))
                (=>
                    (and
                        (q_reaches_b665189a22a9bc20b75324461c8c5287<a0> (tuple_proj<a0-a1>.0 self_) zm)
                        (q_step_b665189a22a9bc20645f008c4b764e02<a0> zm ze zn)
                    )
                    (q_pre_next_b665189a22a9bc20c4ab4a1a92847345<a1> (tuple_proj<a0-a1>.1 self_) ze)
                )
            )
        )";
        true
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        // self.iter.completed() && *self.func == !self.func
        "(and
            (q_completed_b665189a22a9bc20aeb347e2b1280c86<a0>
                (mut<a0>
                    (tuple_proj<a0-a1>.0 (mut_current<Tuple<a0-a1>> self_))
                    (tuple_proj<a0-a1>.0 (mut_final<Tuple<a0-a1>> self_))
                )
            )
            (=
                (tuple_proj<a0-a1>.1 (mut_current<Tuple<a0-a1>> self_))
                (tuple_proj<a0-a1>.1 (mut_final<Tuple<a0-a1>> self_))
            )
        )";
        true
    }

    #[thrust_macros::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool {
        // exists(|i: i64| self.iter.step(i, dist.iter)
        //     && pre!(self.func(i)) && post!(self.func(i), item))
        // && self.func == dist.func
        "(exists ((zi Int))
            (and
                (q_step_b665189a22a9bc20645f008c4b764e02<a0> (tuple_proj<a0-a1>.0 self_) zi (tuple_proj<a0-a1>.0 dist))
                (q_pre_next_b665189a22a9bc20c4ab4a1a92847345<a1> (tuple_proj<a0-a1>.1 self_) zi)
                (q_post_next_b665189a22a9bc20c4ab4a1a92847345<a1> (tuple_proj<a0-a1>.1 self_) zi item)
                (= (tuple_proj<a0-a1>.1 self_) (tuple_proj<a0-a1>.1 dist))
            )
        )";
        true
    }

    #[thrust_macros::predicate]
    fn reaches(self, dist: Self) -> bool {
        // self.iter.reaches(dist.iter) && self.func == dist.func
        "(and
            (q_reaches_b665189a22a9bc20b75324461c8c5287<a0> (tuple_proj<a0-a1>.0 self_) (tuple_proj<a0-a1>.0 dist))
            (= (tuple_proj<a0-a1>.1 self_) (tuple_proj<a0-a1>.1 dist))
        )";
        true
    }
}

fn main() {}

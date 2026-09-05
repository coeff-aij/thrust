// FIXME: flaky with pcsat: verifies in ~50s on some runs, Timeout(180s) on others (match &mut self.iter + reassignment)
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60 COAR_IMAGE=coar:latest

// Probe: reborrowing an Option<I> field and then overwriting the field (the Fuse pattern).
#[thrust_macros::context]
trait A {
    #[thrust_macros::requires(Self::p(*self))]
    #[thrust_macros::ensures(Self::p(!self))]
    fn f(&mut self);

    // Same precondition, no postcondition: used by the `fail` twin.
    #[thrust_macros::requires(Self::p(*self))]
    fn g(&mut self);

    #[thrust_macros::predicate]
    fn p(self) -> bool;
}

struct Fz<I> {
    iter: Option<I>,
}

impl<I> thrust_models::Model for Fz<I> {
    type Ty = Fz<I>;
}

#[thrust_macros::context]
impl<I> A for Fz<I>
where
    I: A + thrust_models::Model,
    <I as thrust_models::Model>::Ty: PartialEq,
{
    #[thrust_macros::predicate]
    fn p(self) -> bool {
        // self.iter == None || I::p(self.iter.unwrap())
        "(or
            ((_ is std.option.Option.None<a0>)
                (tuple_proj<std.option.Option<a0>>.0 self_))
            (and
                ((_ is std.option.Option.Some<a0>)
                    (tuple_proj<std.option.Option<a0>>.0 self_))
                (q_p_f3f493b342eb910838cc97bbb7a143cd<a0>
                    (_getstd.option.Option.Some.0<a0>
                        (tuple_proj<std.option.Option<a0>>.0 self_)))))";
        true
    }

    fn g(&mut self) {}

    fn f(&mut self) {
        match &mut self.iter {
            None => {}
            Some(it) => {
                it.f();
                self.iter = None;
            }
        }
    }
}

fn main() {}

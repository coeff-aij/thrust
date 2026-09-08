//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60 COAR_IMAGE=coar:latest

// Probe: matching an Option<I> field in place with `Some(ref mut it)` (alternative to `match &mut self.iter`).
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
                (q_p_ce73a56b450707e9cffd9dab5bf28cbe<a0>
                    (_getstd.option.Option.Some.0<a0>
                        (tuple_proj<std.option.Option<a0>>.0 self_)))))";
        true
    }

    fn g(&mut self) {}

    fn f(&mut self) {
        match self.iter {
            None => {}
            Some(ref mut it) => {
                it.f();
            }
        }
    }
}

fn main() {}

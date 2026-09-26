//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60 COAR_IMAGE=coar:develop-2493045c3

#[thrust_macros::context]
trait A {
    #[thrust_macros::requires(Self::p(*self))]
    #[thrust_macros::ensures(Self::p(!self))]
    fn f(&mut self);

    #[thrust_macros::requires(Self::p(*self))]
    fn g(&mut self);

    #[thrust_macros::predicate]
    fn p(self) -> bool;
}

struct Fz<I> {
    iter: Option<I>,
}

impl<I: thrust_models::Model> thrust_models::Model for Fz<I> {
    type Ty = Fz<<I as thrust_models::Model>::Ty>;
}

#[thrust_macros::context]
impl<I> A for Fz<I>
where
    I: A + thrust_models::Model,
    <I as thrust_models::Model>::Ty: PartialEq,
{
    #[thrust_macros::predicate]
    fn p(self) -> bool {
        // self.iter == None || exists(|i| self.iter == Some(i) && I::p(i))
        self.iter == None
            || thrust_models::exists(|i: <I as thrust_models::Model>::Ty|
                self.iter == Some(i) && I::p(i))
    }

    fn g(&mut self) {}

    fn f(&mut self) {
        match &mut self.iter {
            None => {}
            Some(it) => {
                it.f();
            }
        }
    }
}

fn main() {}

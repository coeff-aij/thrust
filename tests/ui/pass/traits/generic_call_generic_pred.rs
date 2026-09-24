//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest
// A generic function whose contract names a trait predicate, calling another generic
// function whose contract names the same predicate. Both declare their type parameter
// at the same position, so the predicate instance the call site applies has to be
// chosen by the caller's parameter, not the callee's.
use thrust_models::Model;

#[thrust_macros::context]
trait Counter
where
    Self: Model,
    <Self as Model>::Ty: Model<Ty = <Self as Model>::Ty>,
{
    #[thrust_macros::requires(Self::running(*self))]
    #[thrust_macros::ensures(Self::running(!self))]
    fn tick(&mut self);

    #[thrust_macros::predicate]
    fn running(self) -> bool;
}

#[derive(PartialEq)]
struct Cell {
    n: i64,
}

impl Model for Cell {
    type Ty = Cell;
}

#[thrust_macros::context]
impl Counter for Cell {
    fn tick(&mut self) {
        self.n += 1;
    }

    #[thrust_macros::predicate]
    fn running(self) -> bool {
        // self.n >= 0
        "(>= (tuple_proj<Int>.0 self_) 0)";
        true
    }
}

#[thrust_macros::context]
#[thrust_macros::requires(C::running(*c))]
#[thrust_macros::ensures(C::running(!c))]
fn tick_twice<C: Counter + Model>(c: &mut C)
where
    <C as Model>::Ty: Model<Ty = <C as Model>::Ty>,
{
    c.tick();
    c.tick();
}

#[thrust_macros::context]
#[thrust_macros::requires(C::running(*c))]
#[thrust_macros::ensures(C::running(!c))]
fn tick_four<C: Counter + Model>(c: &mut C)
where
    <C as Model>::Ty: Model<Ty = <C as Model>::Ty>,
{
    tick_twice(c);
    tick_twice(c);
}

fn main() {
    let mut cell = Cell { n: 0 };
    tick_four(&mut cell);
}

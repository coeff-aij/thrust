//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60

// An adapter-shaped method over a generic inner value. The loop carries a rebinding
// of the receiver, so a hand-written invariant has to name the receiver's value on
// entry as well: it does so through a `FnParam<&mut Self>` binder called `self`,
// exactly as it would for a named `&mut` parameter. Without the entry value the
// invariant cannot say that the receiver is the one it started as, nor tie the two
// prophecies together, and the postcondition does not follow.
use thrust_models::{FnParam, Model};
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
#[thrust::trusted]
fn rand() -> bool {
    unimplemented!()
}

#[derive(PartialEq)]
struct Wrap<I> {
    inner: I,
    n: i64,
}

impl<I: Model> Model for Wrap<I> {
    type Ty = Wrap<<I as Model>::Ty>;
}

#[thrust_macros::context]
impl<I> Wrap<I>
where
    I: Model,
{
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(!self == *self)]
    fn spin(&mut self) {
        let s = self;
        while rand() {
            thrust_macros::invariant!(
                |s: &mut Wrap<I>, self: FnParam<&mut Self>|
                    *s == *self.at_entry() && !s == !self.at_entry()
            );
            s.n += 1;
            s.n -= 1;
        }
    }
}

fn main() {}

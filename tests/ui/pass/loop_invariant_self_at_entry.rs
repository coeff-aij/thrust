//@check-pass
//@compile-flags: -C debug-assertions=off

// A loop invariant names the receiver's value on entry the same way it names any
// other parameter's: a `FnParam<..>` binder called `self`, read with `at_entry()`.
// The loop carries a rebinding of the receiver, so the invariant needs both that
// loop-carried value and the entry value to tie the two prophecies together.

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
#[thrust::trusted]
fn rand() -> bool {
    unimplemented!()
}

#[derive(PartialEq, Clone, Copy)]
struct Counter {
    value: i64,
}

impl thrust_models::Model for Counter {
    type Ty = Counter;
}

#[thrust_macros::context]
impl Counter {
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures((!self).value >= (*self).value)]
    fn climb(&mut self) {
        let s = self;
        while rand() {
            thrust_macros::invariant!(
                |s: &mut Counter, self: thrust_models::FnParam<&mut Self>|
                    (*s).value >= (*self.at_entry()).value && !s == !self.at_entry()
            );
            s.value += 1;
        }
    }
}

fn main() {
    let mut c = Counter { value: 3 };
    c.climb();
}

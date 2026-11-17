//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A loop invariant names a parameter's value on entry as `old!(x)` while it also names the
// parameter's value at the loop head as `x`: the loop keeps using `self` and `v` themselves.

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
        while rand() {
            thrust_macros::invariant!(
                |self: &mut Counter, old!(self): &mut Self|
                    (*self).value >= (*old!(self)).value && !self == !old!(self)
            );
            self.value += 1;
        }
    }
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result.len() == v.len() + 2)]
#[thrust_macros::context]
fn push_two(mut v: Vec<i64>) -> Vec<i64> {
    let mut i = 0_i64;
    while i < 2 {
        thrust_macros::invariant!(
            |i: i64, v: Vec<i64>, old!(v): Vec<i64>| v.len() == old!(v).len() + i && i <= 2
        );
        v.push(i);
        i += 1;
    }
    v
}

fn main() {
    let mut c = Counter { value: 3 };
    c.climb();
    let v = push_two(Vec::new());
    assert!(v.len() == 2);
}

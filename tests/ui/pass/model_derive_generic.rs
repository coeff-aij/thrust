//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off

// `derive(Model)` on a generic, a tuple and a unit struct.

use std::marker::PhantomData;

#[derive(thrust_macros::Model)]
struct Tagged<T> {
    tag: u8,
    value: T,
    marker: PhantomData<T>,
}

#[derive(thrust_macros::Model)]
struct Meters(u64);

#[derive(thrust_macros::Model)]
struct Unit;

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result.tag == 1 && result.value == x)]
fn tag(x: Meters) -> Tagged<Meters> {
    Tagged {
        tag: 1,
        value: x,
        marker: PhantomData,
    }
}

#[thrust_macros::requires(m.0 < 100)]
#[thrust_macros::ensures(result == MetersModel(m.0 + 1))]
fn step(_u: Unit, m: Meters) -> Meters {
    Meters(m.0 + 1)
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result.value == MetersModel(1))]
fn tagged_step() -> Tagged<Meters> {
    tag(step(Unit, Meters(0)))
}

fn main() {}

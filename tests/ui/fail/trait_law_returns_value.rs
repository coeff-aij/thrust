//@compile-flags: -C debug-assertions=off

// A law states a property of its arguments and returns `()`: its `result` would be the value the
// implementation's body returns, which the law cannot name.
#[thrust_macros::context]
trait P {
    #[thrust_macros::predicate]
    fn p(self) -> bool;

    #[thrust_macros::law]
    #[thrust_macros::ensures(result)]
    fn l(a: &Self) -> bool; //~ ERROR: returns `bool`
}

fn main() {}

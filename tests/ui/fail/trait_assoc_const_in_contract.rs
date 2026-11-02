//@compile-flags: -C debug-assertions=off

// The value of an associated const of `Self` is not known in a trait method's contract.
#[thrust_macros::context]
trait Tr {
    const K: i64;

    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(result == Self::K)] //~ ERROR: cannot be evaluated in a formula
    fn get(&self) -> i64;
}

struct B;

#[thrust_macros::context]
impl Tr for B {
    const K: i64 = 1;

    fn get(&self) -> i64 {
        1
    }
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == 0)]
fn through_param<T: Tr>(t: &T) -> i64 {
    t.get()
}

fn main() {
    let _ = through_param(&B);
}

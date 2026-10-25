//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A generic function reads `Source::Item` through a type parameter, where its contract has no
// invariant, and passes it to `Item`'s `bump`: an associated type that holds a type with an
// invariant is rejected.
#[thrust_macros::context]
trait Counter {
    #[thrust_macros::ensures(result <= 100)]
    fn bump(&mut self) -> u32;
}

struct C {
    n: u32,
}

impl thrust_models::Model for C {
    type Ty = Self;
}

#[thrust_macros::context]
impl Invariant for C {
    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        self.n % 2 == 0
    }
}

impl Counter for C {
    fn bump(&mut self) -> u32 {
        if self.n % 2 == 1 { 1000 } else { 0 }
    }
}

trait Source {
    type Item: Counter;
    fn take(&self) -> Option<Self::Item>;
}

struct S;

impl thrust_models::Model for S {
    type Ty = ();
}

impl Source for S {
    type Item = C; //~ ERROR: which has an invariant
    fn take(&self) -> Option<C> {
        Some(C { n: 1 })
    }
}

#[thrust_macros::ensures(result <= 100)]
fn g<T: Source>(s: &T) -> u32 {
    match s.take() {
        Some(mut c) => c.bump(),
        None => 0,
    }
}

fn main() {
    let r = g(&S);
    assert!(r <= 100);
}

//@compile-flags: -Adead_code -C debug-assertions=off

// `W<T>`'s `clone` is verified over `T` and at the instances verified code calls it at. std's
// `Option::<W<C>>::clone` runs it at `C`, where nothing analyzed it, and it runs `C::clone`, which
// assumes the invariant of a field nobody checked.
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

impl Clone for C {
    fn clone(&self) -> Self { //~ ERROR: which Thrust does not analyze, runs it
        if self.n % 2 == 1 { C { n: 0 } } else { C { n: self.n } }
    }
}

struct W<T>(T);

impl<T: thrust_models::Model> thrust_models::Model for W<T> {
    type Ty = T::Ty;
}

#[thrust_macros::context]
impl<T: Clone + thrust_models::Model> Clone for W<T> {
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(result == *self)]
    fn clone(&self) -> Self {
        W(self.0.clone())
    }
}

fn main() {
    let o = Some(W(C { n: 1 }));
    let p = o.clone();
    match p {
        Some(w) => assert!(w.0.n == 1),
        None => {}
    }
}

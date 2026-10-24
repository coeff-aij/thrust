//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables -A dead_code
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// Unsat. A law of another trait states that `Small` yields nothing where `ok` holds, and `Unit`
// inherits it with `ok` true: the law, checked for `Unit`, and `next`'s rule contradict each
// other whatever relation is inferred, since the derived predicate depends on no forall predicate
// and so cannot be chosen after `ok`.

#[thrust_macros::context]
trait Iter {
    type Item;

    #[thrust_macros::predicate(derived)]
    fn produces(self, item: Self::Item) -> bool;

    #[thrust_macros::ensures(thrust_models::forall(|i| result == Some(i) ==> Self::produces(*self, i)))]
    fn next(&mut self) -> Option<Self::Item>;
}

// Yields 0, 1, 2, 3, 4 from 0.
#[derive(PartialEq)]
struct Small {
    n: isize,
}

impl thrust_models::Model for Small {
    type Ty = Small;
}

#[thrust_macros::context]
impl Iter for Small {
    type Item = isize;

    fn next(&mut self) -> Option<Self::Item> {
        if 0 <= self.n && self.n < 5 {
            let item = self.n;
            self.n += 1;
            Some(item)
        } else {
            None
        }
    }
}

#[thrust_macros::context]
trait Other {
    #[thrust_macros::predicate]
    fn ok(self) -> bool;

    #[thrust_macros::law]
    #[thrust_macros::ensures(Self::ok(*a) ==> !Small::produces(*r, k))]
    fn nothing(a: &Self, r: &Small, k: isize) {}
}

#[derive(PartialEq, Clone, Copy)]
struct Unit;

impl thrust_models::Model for Unit {
    type Ty = Unit;
}

#[thrust_macros::context]
impl Other for Unit {
    #[thrust_macros::predicate]
    fn ok(self) -> bool {
        true
    }
}

#[thrust_macros::requires(T::ok(*t))]
#[thrust_macros::ensures(!Small::produces(*r, k))]
fn g<T: Other + thrust_models::Model>(t: &T, r: &Small, k: isize) where <T as thrust_models::Model>::Ty: thrust_models::Model<Ty = <T as thrust_models::Model>::Ty> {}

fn main() {
    let mut s = Small { n: 0 };
    g(&Unit, &s, 0);
    if let Some(v) = s.next() {
        assert!(false);
    }
}

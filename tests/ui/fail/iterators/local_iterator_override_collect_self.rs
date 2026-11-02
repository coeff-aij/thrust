//@error-in-other-file: cannot be checked against that spec
//@compile-flags: -C debug-assertions=off

// `W<T>`'s `collect`, verified once over `B`, calls itself at `B = Vec<T>`, where it takes
// std.rs's `collect` contract; its body would have to be checked against that contract inside its
// own analysis, so Thrust stops.

#[derive(PartialEq)]
struct W<T: thrust_models::Model> {
    n: i64,
    t: std::marker::PhantomData<T>,
}

impl<T: thrust_models::Model> thrust_models::Model for W<T> {
    type Ty = W<T>;
}

impl<T: Default + thrust_models::Model> Iterator for W<T> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        if self.n < 3 {
            self.n += 1;
            Some(T::default())
        } else {
            None
        }
    }

    fn collect<B: std::iter::FromIterator<T>>(self) -> B {
        if self.n == 1 {
            let v: Vec<T> = W { n: 0, t: std::marker::PhantomData }.collect();
            assert!(v.len() == 3);
        }
        B::from_iter(Vec::<T>::new())
    }
}

#[thrust_macros::context]
impl<T: Default + thrust_models::Model> IteratorSpec for W<T> {
    #[thrust_macros::predicate]
    fn inv(self) -> bool {
        0 <= self.n && self.n <= 3
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Vec<T>, o: Self) -> bool {
        self.n <= o.n && o.n <= 3 && visited.len() == o.n - self.n
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        (*self).n >= 3 && *self == !self
    }

    fn produces_refl(a: &Self) {}

    fn produces_trans(
        a: &Self,
        ab: thrust_models::model::Seq<<T as thrust_models::Model>::Ty>,
        b: &Self,
        bc: thrust_models::model::Seq<<T as thrust_models::Model>::Ty>,
        c: &Self,
    ) {
    }
}

struct Mine;

impl std::iter::FromIterator<i64> for Mine {
    fn from_iter<I: IntoIterator<Item = i64>>(_: I) -> Mine {
        Mine
    }
}

fn main() {
    let _m: Mine = W::<i64> { n: 1, t: std::marker::PhantomData }.collect();
}

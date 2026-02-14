//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=.experimental/thrust-preprocessed-spacer-wrapper

trait Iterator {
    type Item;

    #[thrust::requires(true)]
    #[thrust::ensures(
        (Self::completed(*self) || (exists i:int. (result == std::option::Option::<int>::Some(i)) && Self::step(*self, i, ^self)))
        && (!Self::completed(*self) || (result == std::option::Option::<int>::None() && *self == ^self))
    )]
    fn next(&mut self) -> Option<Self::Item>;

    #[thrust::predicate]
    fn completed(self) -> bool;
    #[thrust::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool;
}

struct Range {
    start: i64,
    end: i64,
}

impl Iterator for Range {
    type Item = i64;

    fn next(&mut self) -> Option<Self::Item> {
        if self.start < self.end {
            let item = self.start;
            self.start += 1;
            Some(item)
        } else {
            None
        }
    }

    #[thrust::predicate]
    fn completed(self) -> bool {
        "(not (<
            (tuple_proj<Int-Int>.0 self)
            (tuple_proj<Int-Int>.1 self)
        ))";
        true
    }

    #[thrust::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool {
        "(and
            (= (tuple_proj<Int-Int>.1 self) (tuple_proj<Int-Int>.1 dist))
            (= (tuple_proj<Int-Int>.0 self) item)
            (= (+ (tuple_proj<Int-Int>.0 self) 1) (tuple_proj<Int-Int>.0 dist))
        )";
        true
    }
}

struct Id {
    iter: Range,
}

impl Iterator for Id {
    type Item = <Range as Iterator>::Item;

    fn next(&mut self) -> Option<<Range as Iterator>::Item> {
        self.iter.next()
    }

    #[thrust::predicate]
    fn completed(self) -> bool {
        // self.iter.completed()
        "(Range_completed (tuple_proj<Tuple<Int-Int>>.0 self))";
        true
    }

    #[thrust::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool {
        // self.iter.step(item, dist)
        "(Range_step
            (tuple_proj<Tuple<Int-Int>>.0 self)
            item
            (tuple_proj<Tuple<Int-Int>>.0 dist)
        )";
        true
    }
}

fn main() {
    let mut range = Range { start: 0, end: 5 };

    let mut adapter = Id { iter: range };

    let mut count = 0;
    let mut sum = 0;
    while let Some(i) = adapter.next() {
        count += 1;
        sum += i;
    }

    assert!(count == 5);
    assert!(sum == 10);
}

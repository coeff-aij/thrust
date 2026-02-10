//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

trait Iterator {
    type Item;
    
    // #[thrust::trusted]
    // #[thrust::requires(true)]
    // #[thrust::ensures(
    //     (Self::completed(*self, ^self) || (exists i:int. (result == std::option::Option::<int>::Some(i)) && Self::step(*self, i, ^self)))
    //     && (!Self::completed(*self, ^self) || (result == std::option::Option::<int>::None() && *self == ^self))
    // )]
    fn next(&mut self) -> Option<Self::Item>;
    
    #[thrust::predicate]
    fn completed(self, dist: Self) -> bool;
    #[thrust::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool;
}


struct Range {
    start: i64,
    end: i64,
}

impl Iterator for Range {
    type Item = i64;

    #[thrust::trusted]
    #[thrust::requires(true)]
    #[thrust::ensures(
        (Self::completed(*self, ^self) || (exists i:int. (result == std::option::Option::<int>::Some(i)) && Self::step(*self, i, ^self)))
        && (!Self::completed(*self, ^self) || (result == std::option::Option::<int>::None() && *self == ^self))
    )]
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
    fn completed(self, dist: Self) -> bool {
        "(and
            (not (<
                (tuple_proj<Int-Int>.0 self)
                (tuple_proj<Int-Int>.1 self)
            ))
            (= self dist)
        )"; true
    }

    #[thrust::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool {
        "(and
            (= (tuple_proj<Int-Int>.1 self) (tuple_proj<Int-Int>.1 dist))
            (= (tuple_proj<Int-Int>.0 self) item)
            (= (+ (tuple_proj<Int-Int>.0 self) 1) (tuple_proj<Int-Int>.0 dist))
        )"; true
    }
}

struct Take {
    iter: Range,
    n: i64,
}

impl Iterator for Take
{
    type Item = <Range as Iterator>::Item;

    #[thrust::trusted]
    #[thrust::requires(true)]
    #[thrust::ensures(
        (Self::completed(*self, ^self) || (exists i:int. (result == std::option::Option::<int>::Some(i)) && Self::step(*self, i, ^self)))
        && (!Self::completed(*self, ^self) || (result == std::option::Option::<int>::None() && *self == ^self))
    )]
    fn next(&mut self) -> Option<<Range as Iterator>::Item> {
        if self.n > 0 {
            self.n -= 1;
            self.iter.next()
        } else {
            None
        }
    }
    
    #[thrust::predicate]
    fn completed(self, dist: Self) -> bool {
        // (self == dist && !(self.n > 0)) || (self.n == dist.n - 1 && self.iter.completed(dist)) is written as following:
        "(or
            (and
                (= self dist)
                (not (> (tuple_proj<Tuple<Int-Int>-Int>.1 self) 0))
            )
            (and
                (=
                    (tuple_proj<Tuple<Int-Int>-Int>.1 self)
                    (+ (tuple_proj<Tuple<Int-Int>-Int>.1 dist) 1)
                )
                (Range_completed (tuple_proj<Tuple<Int-Int>-Int>.0 self) (tuple_proj<Tuple<Int-Int>-Int>.0 dist))
            )
        )"; true
    }

    #[thrust::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool {
        // self.n == dist.n + 1 && self.iter.step(self.iter, item, dist.iter)
        // is written as following:
        "(and
            (=
                (tuple_proj<Tuple<Int-Int>-Int>.1 self)
                (+ (tuple_proj<Tuple<Int-Int>-Int>.1 dist) 1)
            )
            (Range_step
                (tuple_proj<Tuple<Int-Int>-Int>.0 self)
                item
                (tuple_proj<Tuple<Int-Int>-Int>.0 dist)
            )
        )"; true
    }
}

fn main() {
    let mut range = Range {
        start: 0,
        end: 5,
    };

    // let mut taken = Take {
    //     iter: range,
    //     n: 3,
    // };

    let mut count = 0;
    let mut sum = 0;
    while let Some(i) = range.next() {
        count += 1;
        sum += i;
    }

    assert!(count == 5)
    // assert!(count == 3);
    // assert!(sum == 3);
    // assert!(taken.n == 0);
}

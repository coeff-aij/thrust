//@check-pass
//@compile-flags: -C debug-assertions=off

trait Iterator {
    type Item;
    
    #[thrust::requires(true)]
    #[thrust::ensures(
        (completed(*self) || (exists i:int. (result == std::option::Option::<int>::Some(i)) && step(*self, i, ^self)))
        && (!completed(*self) || (result == std::option::Option::<int>::None() && *self == ^self))
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
        ))"; true
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

struct Take<I> {
    iter: I,
    n: i64,
}

impl<I> Iterator for Take<I>
where
    I: Iterator,
{
    type Item = I::Item;

    fn next(&mut self) -> Option<Self::Item> {
        if self.n > 0 {
            self.n -= 1;
            self.iter.next()
        } else {
            None
        }
    }
    
    #[thrust::predicate]
    fn completed(self) -> bool {
        // n <= 0 || { self.iter.completed() } is written as following:
        "(or
            (<= (tuple_proj<Int-Int>.1 self) 0)
            (self_iter_completed())
        ))"; true
    }

    #[thrust::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool {
        // self.iter.step(self.iter, item, dist.iter)
        // is written as following:
        "(self_iter_step(
            (tuple_proj<Int-Int>.0 self)
            item
            (tuple_proj<Int-Int>.0 dist)
        )"; true
    }
}

fn main() {
    let mut range = Range {
        start: 0,
        end: 5,
    };

    let mut taken = Take {
        iter: range,
        n: 3,
    };

    let mut count = 0;
    let mut sum = 0;
    while let Some(i) = taken.next() {
        count += 1;
        sum += i;
    }

    assert!(count == 3);
    // assert!(sum == 10);
    assert!(taken.n == 0);
}

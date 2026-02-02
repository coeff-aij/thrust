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


struct MappedRange<F> {
    start: i64,
    end: i64,
    f: F,
}

impl<F> Iterator for MappedRange<F>
where
    F: Fn(i64) -> i64
{
    type Item = i64;

    fn next(&mut self) -> Option<Self::Item> {
        if self.start < self.end {
            let item = self.start;
            self.start += 1;
            Some((self.f)(item))
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
        "(exists ((v Int) (v' Int) (f F Int -> Int))
            (and
                (= (tuple_proj<Int-Int>.1 self) (tuple_proj<Int-Int>.1 dist))
                (= (tuple_proj<Int-Int>.0 self) v)
                (pre_f(f, v) and post(f, v, f', v'))
                (= v' item)
                (= (+ (tuple_proj<Int-Int>.0 self) 1) (tuple_proj<Int-Int>.0 dist))
            )
        )"; true
    }
}

fn main() {
    let mut mapped_range = MappedRange {
        start: 0,
        end: 5,
        f: |x: i64| { x * 2 }
    };

    let mut count = 0;
    let mut sum = 0;
    let mut last_item = 0;
    while let Some(i) = mapped_range.next() {
        count += 1;
        sum += i;
        last_item = i;
    }

    assert!(count == 5);
    // assert!(sum == 10);
    assert!(last_item == 8);
}

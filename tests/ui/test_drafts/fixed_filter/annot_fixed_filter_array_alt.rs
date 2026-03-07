//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper


trait Iterator {
    type Item;
    
    // #[thrust::requires(true)]
    // #[thrust::ensures(
    //     (Self::completed(*self) || (exists i:int. (result == std::option::Option::<int>::Some(i)) && Self::step(*self, i, ^self)))
    //     && (!Self::completed(*self) || (result == std::option::Option::<int>::None() && *self == ^self))
    // )]
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

    #[thrust::requires(true)]
    #[thrust::ensures(
        (Self::completed(*self) || (exists i:int. (result == std::option::Option::<int>::Some(i)) && Self::step(*self, i, ^self)))
        && (!Self::completed(*self) || (result == std::option::Option::<int>::None() && *self == ^self))
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

struct Filter{
    iter: Range,
    // pred: F,
}

impl Iterator for Filter
// where
//     I: Iterator,
//     F: FnMut(I::Item) -> bool
{
    type Item = <Range as Iterator>::Item;

    // #[thrust::trusted]
    #[thrust::requires(true)]
    #[thrust::ensures(
        // (Self::completed(*self) || (exists i:int. (result == std::option::Option::<int>::Some(i)) && Self::step(*self, i, ^self)))
        // && (!Self::completed(*self) || (result == std::option::Option::<int>::None() && *self == ^self))
        (exists i:int. ((result == std::option::Option::<int>::Some(i)) && Self::step(*self, i, ^self)))
        && (!(result == std::option::Option::<int>::None()) || Self::completed(*self, ^self))
    )]
    fn next(&mut self) -> Option<Self::Item> {
        while let Some(item) = self.iter.next() {
            // if self.pred(item) {
            if item >= 2 {
                return Some(item)
            }
        }
        None
    }
    
    #[thrust::predicate]
    fn completed(self, dist: Self) -> bool {
        // self.iter.completed()
        "(exists (
            (it (Array Int A1_Tuple<Int-Int>)) (v (Array Int Int)) (l Int)
        ) (and
            (and
                (= (select it 0) (tuple_proj<Tuple<Int-Int>>.0 self))
                (Range_step (select it (- l 1)) item (tuple_proj<Tuple<Int-Int>>.0 dist))
                (not (>= item 2))
            )
            (forall ((i Int)) (and
                (<= 0 i)
                (< i (- l 1))
                (Range_step (select it i) (select v i) (select it (+ i 1)))
                (not (>= (select v i) 2))
            ))
        ))"; true
    }

    #[thrust::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool {
        "(exists (
            (it (Array Int A1_Tuple<Int-Int>)) (v (Array Int Int)) (l Int)
        ) (and
            (and
                (= (select it 0) (tuple_proj<Tuple<Int-Int>>.0 self))
                (Range_step (select it (- l 1)) item (tuple_proj<Tuple<Int-Int>>.0 dist))
                (>= item 2)
            )
            (forall ((i Int)) (and
                (<= 0 i)
                (< i (- l 1))
                (Range_step (select it i) (select v i) (select it (+ i 1)))
                (not (>= (select v i) 2))
            ))
        ))"; true
    }
}

fn main() {
    let mut range = Range { start: 0, end: 5 };

    let mut adapter = Filter { iter: range };

    let mut count = 0;
    let mut sum = 0;
    let mut last = None;
    while let Some(i) = adapter.next() {
        count += 1;
        sum += i;
        last = Some(i);
    }

    // assert!(count == 3);
    // assert!(sum == 9);
    assert!(matches!(last, Some(x) if x >= 2));
}

//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

#![feature(custom_inner_attributes)]
#![thrust::raw_command("(declare-fun FixedFilter_iter_completed (A1_Tuple<Int-Int>) Bool)
(declare-fun FixedFilter_iter_step (A1_Tuple<Int-Int> Int A1_Tuple<Int-Int>) Bool)")]

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

struct FixedFilter {
    iter: Range,
}

impl Iterator for FixedFilter
{
    type Item = <Range as Iterator>::Item;

    fn next(&mut self) -> Option<<Range as Iterator>::Item> {
        while let Some(item) = self.iter.next() {
            if item >= 2 {
                return Some(item)
            }
        }
        None
    }
    
    #[thrust::predicate]
    fn completed(self) -> bool {
        // self.iter.completed()
        "(FixedFilter_iter_completed (tuple_proj<Tuple<Int-Int>>.0 self))"; true
    }

    #[thrust::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool {
        // (exists via: Self. exists via_item Int. self.iter.step(via_item, via.iter)) && item >= 2
        "(and
            (exists ((via A3_Tuple<Tuple<Int-Int>>) (via_item Int))
                (FixedFilter_iter_step
                    (tuple_proj<Tuple<Int-Int>>.0 self)
                    via_item
                    (tuple_proj<Tuple<Int-Int>>.0 via)
                )
            )
            (>= item 2)
        )"; true
    }
}

fn main() {
    let mut range = Range { start: 0, end: 5 };

    let mut adapter = FixedFilter { iter: range };

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

//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=.experimental/thrust-preprocessed-gspacer-wrapper

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
}

fn main() {
    let mut range = Range {
        start: 0,
        end: 5,
    };

    let mut adapter = FixedFilter {
        iter: range,
    };

    let mut count = 0;
    let mut sum = 0;
    let mut last = None;
    while let Some(i) = adapter.next() {
        count += 1;
        sum += i;
        last = Some(i);
    }

    assert!(count == 3);
    // assert!(sum == 10);
    assert!(matches!(last, Some(x) if x >= 2));
}

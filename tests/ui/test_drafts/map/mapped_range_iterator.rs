//@check-pass
//@compile-flags: -C debug-assertions=off

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

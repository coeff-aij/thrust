//@check-pass
//@compile-flags: -C debug-assertions=off

trait Iterator<T> {
    fn next(&mut self) -> Option<T>;
}

struct Range {
    start: i64,
    end: i64,
}

impl Iterator<i64> for Range {
    fn next(&mut self) -> Option<i64> {
        if self.start < self.end {
            let item = self.start;
            self.start += 1;
            Some(item)
        } else {
            None
        }
    }
}

impl Iterator<i32> for Range {
    fn next(&mut self) -> Option<i32> {
        if self.start < self.end {
            let item = self.start;
            self.start += 1;
            Some(item as i32)
        } else {
            None
        }
    }
}

fn main() {
    let mut range = Range {
        start: 0,
        end: 5,
    };

    let mut count = 0;
    let mut sum = 0;
    while let Some(i) = Iterator::<i32>::next(&mut range) {
        count += 1;
        sum += i;
    }

    assert!(count == 5);
    assert!(sum == 10);
    assert!(range.start > 0);
}
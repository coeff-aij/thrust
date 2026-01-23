//@check-pass
//@compile-flags: -C debug-assertions=off

trait Iterator {
    type Item;
    
    #[thrust::requires(true)]
    #[thrust::ensures(
        match result {
            Some(i) => (*self).step(i, ^self),
            None => (*self).completed(),
        }
    )]
    fn next(&mut self) -> Option<Self::Item>;
    
    #[thrust::predicate]
    fn completed(&self) -> bool;
    #[thrust::predicate]
    fn step(&self, item: Self::Item, dist: &Self) -> bool;
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
    fn completed(&self) -> bool {
        self.start < self.end
    }

    #[thrust::predicate]
    fn step(&self, item: Self::Item, dist: &Self) -> bool {
        self.end == dist.end
        && self.start == item
        && self.start + 1 == dist.start
    }
}

fn main() {
    let mut range = Range {
        start: 0,
        end: 5,
    };

    let mut count = 0;
    let mut sum = 0;
    loop {
        assert!(count == range.start);

        let Some(i) = range.next() else {
            break;
        };
        assert!(range.start < range.end);

        count += 1;
        sum += i;
    }

    assert!(range.start >= range.end);
    assert!(count == range.start);

    assert!(count == 5);
    assert!(sum == 10);
}

trait Iterator<T> {
    type Item = T;
    
    #[thrust::requires(true)]
    #[thrust::ensures(
        match result {
            Some(i) => (*self).step(i, ^self),
            None => (*self).completed(),
        }
    )]
    fn next(&mut self) -> Option<Item>;
    
    #[thrust::predicate]
    fn completed(&self) -> bool;
    #[thrust::predicate]
    fn step(&self) -> bool;
}

struct Take<I>
where
    I: Iterator
{
    iter: I,
    n: usize,
}

impl<I> Iterator<I::Item> for Take<I> {
    type Item = I::Item;

    fn next(&mut self) -> Option<Item> {
        if self.n == 0 {
            None
        } else {
            self.n -= 1;
            self.iter.next()
        }
    }

    #[thrust::predicate]
    fn completed(&self) -> bool {
        self.n == 0 || self.iter.completed()
    }

    #[thrust::predicate]
    fn step(&self, &item: Item) -> bool {
        self.inner.step(item)
    }
}

fn main() {
    let mut range = Range {
        start: 0,
        end: 5,
    };

    let mut taken = Take {
        iter: range,
        n: 2,
    };

    let mut count = 0;
    let mut sum = 0;
    loop {
        assert!(count == range.start);

        let Some(i) = next(&mut range) else {
            break;
        };
        assert!(range.start < range.end);

        count += 1;
        sum += i;
    }

    assert!(range.start >= range.end);
    assert!(count == range.start);

    assert!(count == 5);
    assert!(sum == 15);

    let v = vec![0..10];
    v.iter().map(|&mut x| x *= 2);
}
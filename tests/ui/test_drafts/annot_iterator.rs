//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off

// This is a draft of the feature which supports
// annotations about iterator traits.

// This struct is used to represent the sequence of
// items produced from iterator.
enum List<T> {
    Cons(T, Box<List>),
    Nil,
}

fn length<T>(la: &List<T>) -> i32 {
    match la {
        List::Cons(_, lb) => length(lb) + 1,
        List::Nil => 0,
    }
}

fn singleton<T>(item: T) -> List<T> {
    List::Cons(item, List::Nil)
}

fn empty<T>() -> List<T> {
    List::Nil
}

fn get<T>(list: &List<T>, idx: i32) -> Option<i32> {
    if idx == 0 {
        match list {
            List::Cons(head, _) => Some(head),
            List::Nil => None,
        }
    } else {
        match list {
            List::Cons(_, tail) => get(tail, idx - 1),
            List::Nil => None,
        }
    }
}

fn push<T>(list: &List<T>, item: T) -> List<T> {
    List::Cons(item, list)
}

trait Iterator {
    type Item;

    // predicates
    #[thrust::predicate]
    fn completed(&self) -> bool;
    #[thrust::predicate]
    fn produces(&self, list: List<self::Item>, &dist: Self) -> bool;


    // CREUSOT-style
    #[law]
    #[thrust::ensures(a.produces(List<Self::Item>::Nil, a))]
    fn produces_refl(&a: Self);

    #[law]
    #[thrust::requires(a.produces(ab, b) && b.produces(bc, c))]
    #[thrust::ensures(a.produces(concat(ab, bc), c))]
    fn produces_trans(&a: Self, ab: List<Self::Item>, &b: Self, bc: List<Self::Item>, &c: Self) -> bool;

    #[thrust::ensures((result == Some(a)
    ==> !self.completed() && self.produces(singleton<Self::Item>(a), ^self))
    && (result == None ==> self.completed()))]
    fn next(&mut self) -> Option<Self::Item>;
}

#[derive(Clone)]
struct RangeIterator {
    start: usize, // treat as integer for now
    end: usize,
}

// Thrust has
// {DefId -> refinement types}

// {Iterator -> {
//      next -> {requires = , ensures = ,} concrete method is unknown here
//      ...
// }}

// {RangeIterator -> Iterator(defId = ...) pick annotations from table or parsed everytime
//      produces() := { definition or infered }
//      next() -> {input_type -> return_type} (refinement types)
// } 

// iter.next(): call to RangeIterator::next()

impl Iterator for RangeIterator {
    type Item = usize;
    #[thrust::predicate]
    fn produces(&self, list: List<self::Item>, &dist: Self) -> bool {
        if self.end != dist.end {
            return false;
        }

        // Check if `list` equals to `[self.start .. dist.start]`

        // using `forall` quantifier
        forall i. (0 <= i && i < dist.start - self.start)
            => list.get(i) == Some(self.start + i) // list.get(i) is also recursive
        // or recursive definition
        match list {
            Cons(head, tail) => head == self.start
                && Self::produces(
                    Self{start: self.start + 1, end: self.end},
                    tail,
                    dist.start
                ),
            Nil => true,
        }

        // "(some-definition)"; true
    }

    #[thrust::predicate]
    fn completed(&self) -> bool {
        self.start >= self.end
    }

    fn next(&mut self) -> Option<Self::Item> {
        if self.start < self.end {
            let v = self.start;
            self.start += 1;
            Some(v)
        } else {
            None
        }
    }
}

fn main() {
    let mut iter = RangeIterator{start: 0, end: 10};

    for x in iter {
        // some computation
    }
    // will be verified as following:

    let mut count = 0;
    let mut sum = 0;

    let init_iter = iter.clone();
    let mut produced = List<i32>::Nil;
    loop {
        assert!(init_iter.produces(produced, iter));
        match iter.next() { // we know the defid of RangeIterator::next()
            None => break,
            Some(x) => {
                produced = push<i32>(produced, x);

                // some computation
                count += 1;
                sum += x;
            }
        }
    }
    assert!(count == 10);
    assert!(sum == );
    assert!(produced == 0..10);
}
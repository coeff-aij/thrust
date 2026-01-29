//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=thrust-pcsat-wrapper

struct Range {
    start: i64,
    end: i64,
}

impl Range {
    #[thrust::requires(true)]
    #[thrust::ensures(
        (exists i:int. (result == std::option::Option::<int>::Some(i)) && step(*self, i, ^self))
        || ((result == std::option::Option::<int>::None()) && completed(*self))
    )]
    fn next(&mut self) -> Option<i64> {
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
        // (tuple_proj<Int-Int>.0 self) is equivalent to self.start
        // self.start < self.end is written as following:
        "(not (<
            (tuple_proj<Int-Int>.0 self)
            (tuple_proj<Int-Int>.1 self)
        ))"; true
    }

    #[thrust::predicate]
    fn step(self, item: i64, dist: Self) -> bool {
        "(and
            (= (tuple_proj<Int-Int>.1 self) (tuple_proj<Int-Int>.1 dist))
            (= (tuple_proj<Int-Int>.0 self) item)
            (= (+ (tuple_proj<Int-Int>.0 self) 1) (tuple_proj<Int-Int>.0 dist))
        )"; true
    }
}

fn main() {
    let mut range = Range {
        start: 0,
        end: 5,
    };

    let opt = range.next();
    assert!(matches!(opt, Some(0)));
    assert!(range.start == 1 && range.end == 5)
}
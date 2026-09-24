//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60 COAR_IMAGE=coar:develop-2493045c3

// A generic adapter nested in itself at a call site.
//
// `Take<Take<Range>>` needs `Take`'s invariant at two instantiations, and the
// outer one is stated through the inner one, which is stated through `Range`'s.
// Entering `next` there holds only if all three are read in turn.
use thrust_models::Model;

#[thrust_macros::context]
trait Iterator {
    type Item;

    #[thrust_macros::requires(Self::invariant(*self))]
    #[thrust_macros::ensures(Self::invariant(!self))]
    fn next(&mut self) -> Option<Self::Item>;

    #[thrust_macros::predicate]
    fn invariant(self) -> bool;
}

#[derive(PartialEq)]
struct Take<I> {
    iter: I,
    n: usize,
}

impl<I> Model for Take<I> {
    type Ty = Take<I>;
}

#[thrust_macros::context]
impl<I> Iterator for Take<I>
where
    I: Iterator + Model,
    <I as Iterator>::Item: Model,
    <I as Model>::Ty: PartialEq,
{
    type Item = I::Item;

    fn next(&mut self) -> Option<I::Item> {
        if self.n != 0 {
            self.n -= 1;
            self.iter.next()
        } else {
            None
        }
    }

    // self.iter.invariant() && self.n >= 0
    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        "(and
            (q_invariant_3b91c5ccd4337d12ed230c5660d38780<a0> (tuple_proj<a0-Int>.0 self_))
            (>= (tuple_proj<a0-Int>.1 self_) 0))";
        true
    }
}

#[derive(PartialEq)]
struct Range {
    start: i64,
    end: i64,
}

impl Model for Range {
    type Ty = Range;
}

#[thrust_macros::context]
impl Iterator for Range {
    type Item = i64;

    fn next(&mut self) -> Option<i64> {
        if self.start < self.end {
            let item = self.start;
            self.start += 1;
            Some(item)
        } else {
            None
        }
    }

    // self.start <= self.end
    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        "(<= (tuple_proj<Int-Int>.0 self_) (tuple_proj<Int-Int>.1 self_))";
        true
    }
}

fn main() {
    let mut t = Take {
        iter: Take {
            iter: Range { start: 0, end: 3 },
            n: 2,
        },
        n: 1,
    };
    let _ = t.next();
}

// `tests/ui/pass/iterators/std_map.rs` (`for` over std's `Map`, generic in the closure), with
// `n == produced.len()` added to the invariant, which names `iter_old` and `produced`.

use thrust_models::model::{Closure, Int, Mut, Seq};
use thrust_models::{forall, Ghost};

#[thrust_macros::context]
#[thrust_macros::requires(forall(|c: Closure<F>, x: Int| !(0 <= x && x < 1000) || thrust_macros::pre!(c(x))))]
#[thrust_macros::requires(forall(|c: Closure<F>, d: Closure<F>, x: Int, y: Int| !thrust_macros::post!(Mut::new(c, d)(x), y) || y == x * 2))]
#[thrust_macros::ensures(result == 10)]
fn count_nonneg<F: FnMut(i64) -> i64>(f: F) -> i64 {
    let mut n = 0;
    for y in (0..10).map(f) {
        thrust_macros::invariant!(|iter: core::iter::Map<core::ops::Range<i64>, F>,
                                   iter_old: Ghost<core::iter::Map<core::ops::Range<i64>, F>>,
                                   produced: Ghost<Seq<Int>>, n: i64|
            <core::iter::Map<core::ops::Range<i64>, F> as IteratorSpec>::inv(iter)
                && iter.0.end == 10 && 0 <= iter.0.start && iter.0.start <= 10 && n == iter.0.start
                && n == produced.len()
                && forall(|c: Closure<F>, d: Closure<F>, x: Int, y: Int| !thrust_macros::post!(Mut::new(c, d)(x), y) || y == x * 2));
        if y >= 0 {
            n += 1;
        }
    }
    n
}

fn main() {
    let f = thrust_macros::closure!(
        requires(0 <= x && x < 1000),
        ensures(result == x * 2),
        |x: i64| -> i64 { x * 2 }
    );
    assert!(count_nonneg(f) == 10);
}

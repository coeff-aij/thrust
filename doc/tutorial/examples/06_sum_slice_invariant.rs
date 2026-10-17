use thrust_models::model::{Int, Seq};
use thrust_models::Ghost;

#[thrust_macros::context]
#[thrust_macros::ensures(result <= 100 * v.len())]
fn sum_capped(v: &Vec<i64>) -> i64 {
    let mut s = 0;
    for x in v.iter() {
        thrust_macros::invariant!(|iter: core::slice::Iter<'_, i64>,
                                   iter_old: Ghost<core::slice::Iter<'_, i64>>,
                                   produced: Ghost<Seq<Int>>,
                                   s: i64,
                                   v: thrust_models::FnParam<&Vec<i64>>|
            iter_old.0 == *v.at_entry() && iter_old.1 == 0 && s <= 100 * produced.len());
        if *x <= 100 {
            s += *x;
        } else {
            s += 100;
        }
    }
    s
}

fn main() {}

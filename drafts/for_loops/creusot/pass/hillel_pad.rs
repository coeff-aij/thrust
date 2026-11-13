//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables -A dead_code
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120
// Creusot's `right_pad` and `left_pad` (`examples/hillel.rs`, 3620de437), with Creusot's code and
// Thrust's annotations: `while` loops that call `Vec::push` and `Vec::insert` (std.rs's contracts).
// Creusot's `snapshot!` values are `ghost!` values, and the parameter `str` is rebound as `s` so
// that the invariant can name both the loop's reference and the entry value of the parameter.
use thrust_models::model::{Int, Seq};
use thrust_models::{forall, FnParam, Ghost, Model};

#[thrust_macros::context]
#[thrust_macros::ensures((!str).len() >= len && (!str).len() >= (*str).len())]
#[thrust_macros::ensures((!str).len() == len || (!str).len() == (*str).len())]
#[thrust_macros::ensures(len <= (*str).len() ==> (!str).len() == (*str).len())]
#[thrust_macros::ensures(len > (*str).len() ==> (!str).len() == len)]
#[thrust_macros::ensures(forall(|i: Int| !(0 <= i && i < (*str).len()) || (!str)[i] == (*str)[i]))]
#[thrust_macros::ensures(forall(|i: Int| !((*str).len() <= i && i < len) || (!str)[i] == pad))]
fn right_pad<T: Copy + Model>(str: &mut Vec<T>, len: usize, pad: T)
where
    <T as Model>::Ty: Model<Ty = <T as Model>::Ty>,
{
    let old_str = thrust_macros::ghost!(|str: &mut Vec<T>| -> Seq<<T as Model>::Ty> { *str });
    let s = str;

    while s.len() < len {
        thrust_macros::invariant!(|s: &mut Vec<T>, str: FnParam<&mut Vec<T>>, old_str: Ghost<Seq<<T as Model>::Ty>>, len: usize, pad: T|
            !s == !str.at_entry() && old_str == *str.at_entry()
                && old_str.len() <= (*s).len()
                && (old_str.len() < len ==> (*s).len() <= len)
                && ((*s).len() > len ==> (*s).len() == old_str.len())
                && forall(|i: Int| !(0 <= i && i < old_str.len()) || (*s)[i] == old_str[i])
                && forall(|i: Int| !(old_str.len() <= i && i < (*s).len()) || (*s)[i] == pad));
        s.push(pad);
    }
}

#[thrust_macros::context]
#[thrust_macros::ensures((!str).len() >= len && (!str).len() >= (*str).len())]
#[thrust_macros::ensures((!str).len() == len || (!str).len() == (*str).len())]
#[thrust_macros::ensures(forall(|i: Int| !(0 <= i && i < ((!str).len() - (*str).len())) || (!str)[i] == pad))]
#[thrust_macros::ensures(forall(|i: Int| !(0 <= i && i < (*str).len()) || (!str)[i + ((!str).len() - (*str).len())] == (*str)[i]))]
fn left_pad<T: Copy + Model>(str: &mut Vec<T>, len: usize, pad: T)
where
    <T as Model>::Ty: Model<Ty = <T as Model>::Ty>,
{
    let old_str = thrust_macros::ghost!(|str: &mut Vec<T>| -> Seq<<T as Model>::Ty> { *str });
    let mut c = thrust_macros::ghost!(|| -> Int { 0 });
    let s = str;

    while s.len() < len {
        thrust_macros::invariant!(|s: &mut Vec<T>, str: FnParam<&mut Vec<T>>, old_str: Ghost<Seq<<T as Model>::Ty>>, c: Ghost<Int>, len: usize, pad: T|
            !s == !str.at_entry() && old_str == *str.at_entry()
                && old_str.len() <= (*s).len()
                && (old_str.len() < len ==> (*s).len() <= len)
                && ((*s).len() > len ==> (*s).len() == old_str.len())
                && c == (*s).len() - old_str.len()
                && forall(|i: Int| !(c <= i && i < (*s).len()) || (*s)[i] == old_str[i - c])
                && forall(|i: Int| !(0 <= i && i < c) || (*s)[i] == pad));
        s.insert(0, pad);
        c = thrust_macros::ghost!(|c: Ghost<Int>| -> Int { 1 + c });
    }
}

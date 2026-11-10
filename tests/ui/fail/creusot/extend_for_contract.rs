//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables -A dead_code
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A second fail twin of extend_for.rs, on `extend` itself: its postcondition appends what the
// iterator produced twice, which is false as soon as one item is produced. The file has no client,
// whose assertion could be refuted through this postcondition whatever the loop does.
// Creusot's `extend` and `extend_index` (`examples/iterators/08_collect_extend.rs`, 3620de437),
// with Creusot's code and Thrust's annotations: a `for` loop over an iterator implementing std.rs's
// `IteratorSpec`, whose invariant states Creusot's equation over the snapshot `old_vec` as a
// `partial_invariant!`; what Creusot keeps of the variables the loop does not change is inferred.
// The invariant names the loop's `iter` and `iter_old`, from whose type the history takes its type.
// `I::inv(iter)` is required where Creusot's type invariant holds by typing.
use thrust_models::model::{Mut, Seq};
use thrust_models::{exists, Ghost, Model};

#[thrust_macros::context]
#[thrust_macros::requires(I::inv(iter))]
#[thrust_macros::ensures(exists(|done: <I as Model>::Ty| exists(|fin: <I as Model>::Ty| exists(|prod: Seq<<T as Model>::Ty>|
    I::completed(Mut::new(done, fin)) && I::produces(iter, prod, done) && !vec == (*vec).concat(prod).concat(prod)))))]
fn extend<T: Model, I: IteratorSpec<Item = T>>(vec: &mut Vec<T>, iter: I) {
    let old_vec = thrust_macros::ghost!(|vec: &mut Vec<T>| -> Seq<<T as Model>::Ty> { *vec });
    for x in iter {
        thrust_macros::partial_invariant!(|iter: I, iter_old: Ghost<I>, produced: Ghost<Seq<<T as Model>::Ty>>, vec: &mut Vec<T>, old_vec: Ghost<Seq<<T as Model>::Ty>>|
            *vec == old_vec.concat(produced));
        vec.push(x);
    }
}

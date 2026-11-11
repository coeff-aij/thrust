//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables -A dead_code
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// concat_vec, `extend_index` of the 2022 artifact's `examples/extend.rs`: `v1.extend` over
// `v2.into_iter()`, std's `Vec::extend` under std.rs's contract (Creusot's, creusot-std
// src/std/vec.rs at 3620de437), with the artifact's assertion in Thrust syntax. The current
// Creusot's copy (`08_collect_extend.rs`) calls a local `extend` with a `for` loop instead
// (`extend_for.rs`).
use thrust_models::model::Seq;
use thrust_models::{Ghost, Model};

#[thrust_macros::context]
#[thrust::callable]
fn extend_index(mut v1: Vec<u32>, v2: Vec<u32>) {
    let old1 = thrust_macros::ghost!(|v1: Vec<u32>| -> Seq<<u32 as Model>::Ty> { v1 });
    let old2 = thrust_macros::ghost!(|v2: Vec<u32>| -> Seq<<u32 as Model>::Ty> { v2 });
    v1.extend(v2.into_iter());
    thrust_macros::proof_assert!(|v1: Vec<u32>, old1: Ghost<Seq<<u32 as Model>::Ty>>, old2: Ghost<Seq<<u32 as Model>::Ty>>| v1 == old1.concat(old2));
}

//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// Indexing at an index type that is a projection of a type parameter, as in
// `v[key.into_slice_idx()]`, is specified through the index's `SliceIndexSpec` predicates.

trait Key {
    type Ix: SliceIndexSpec<i32> + std::slice::SliceIndex<[i32], Output = i32>;
}

impl Key for u8 {
    type Ix = usize;
}

#[thrust_macros::context]
#[thrust_macros::requires(<K::Ix as SliceIndexSpec<i32>>::in_bounds(ix, *v))]
#[thrust_macros::ensures(<K::Ix as SliceIndexSpec<i32>>::has_value(ix, *v, result))]
fn get<K: Key>(v: &Vec<i32>, ix: K::Ix) -> i32
where
    K::Ix: Copy,
{
    v[ix]
}

fn main() {
    let mut v = Vec::new();
    v.push(1);
    v.push(2);
    v.push(3);
    assert!(get::<u8>(&v, 2) == 2);
}

//@check-pass
//@compile-flags: -C debug-assertions=off

#[thrust::requires(true)]
#[thrust::ensures(true)]
#[thrust::trusted]
fn rand() -> i64 { unimplemented!() }

#[thrust::requires(true)]
#[thrust::ensures(
    *ma >= *mb && *ma == ^ma && *ma == ^mb ||
    *ma < *mb && *mb == ^ma && *mb == ^mb
)]
fn update_as_max<'a>(ma: &'a mut i64, mb: &'a mut i64) {
    if *ma >= *mb {
        *mb = *ma
      } else {
        *ma = *mb
    }
}

fn main() {
    let mut v = Vec::new();
    v.push(0);

    let a = rand();
    let mut m = a;
    update_as_max(&mut v[0], &mut m);
    assert!(v[0] == m && m >= a);
}

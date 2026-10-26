//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60

// Over two `TrustedRandomAccess` iterators, `Zip::next` answers `None` once the shorter one is
// out, without taking an item from the longer one: the closure, which never returns on 2, is not
// run.
#[thrust_macros::requires((*a).len() == 1 && (*a)[0] == 2 && (*b).len() == 0)]
#[thrust_macros::ensures(true)]
fn first(a: &[u64], b: &[u64]) {
    let f = thrust_macros::closure!(
        requires(true),
        ensures(*w != 2),
        |w: &u64| -> u64 { if *w == 2 { loop {} } *w },
    );
    let mut z = std::iter::zip(a.iter().map(f), b.iter());
    let r = z.next();
    assert!(r.is_none());
}

fn main() {}

//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60

// The closure reads `layout`, captured by `&`, and counts its calls in `calls`, captured by
// `&mut`. Its body assumes that `layout` keeps its value, which its postcondition still states,
// so `count_twice` proves `hist_inv!`; what the body does to `calls` is still checked.
struct Align {
    abi: u64,
    pref: u64,
}

struct Layout {
    i8_align: Align,
    i16_align: Align,
    ptr_align: Align,
    ptr_size: u64,
}

impl Layout {
    fn align_of(&self, kind: u64) -> u64 {
        if kind == 0 {
            self.i8_align.abi
        } else if kind == 1 {
            self.i16_align.pref
        } else {
            self.ptr_align.abi
        }
    }
}

#[thrust_macros::ensures(thrust_macros::hist_inv!(*f, !f))]
fn count_twice<F: FnMut(u64) -> u64>(f: &mut F) {
    f(0);
    f(1);
}

fn main() {
    let layout = Layout {
        i8_align: Align { abi: 1, pref: 1 },
        i16_align: Align { abi: 2, pref: 2 },
        ptr_align: Align { abi: 8, pref: 8 },
        ptr_size: 8,
    };
    let mut calls: u64 = 0;
    let mut key = |kind: u64| -> u64 {
        calls += 1;
        layout.align_of(kind) + layout.ptr_size
    };
    count_twice(&mut key);
    let k = key(2);
    assert!(k == 16);
    // The last call made `calls` at least 1.
    assert!(calls == 0);
}

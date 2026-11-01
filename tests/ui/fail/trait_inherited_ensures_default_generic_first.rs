//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A trait method's inherited `ensures` holds at a concrete call whichever of the call and a
// generic caller (`get`) is analyzed first.

#[derive(PartialEq)]
enum Tag<V> {
    A(V),
    B,
}

impl<V> thrust_models::Model for Tag<V> {
    type Ty = Tag<V>;
}

#[thrust_macros::context]
trait Tagged {
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(result == 1)]
    fn tag(&self) -> i64 {
        1
    }
}

impl<V> Tagged for Tag<V> {}

fn get<F, V>(_f: F, t: &Tag<V>) -> i64 {
    t.tag()
}
fn main() {
    let t = Tag::<i64>::A(3);
    let _ = get(1i64, &t);
    assert!(t.tag() == 2);
}

// A forwarding impl for `&mut T` reached at `T = dyn Counter`.
#[thrust_macros::context]
trait Counter {
    #[thrust_macros::ensures(result <= 100)]
    fn bump(&mut self) -> u32;
}

struct C;

impl thrust_models::Model for C {
    type Ty = ();
}

impl Counter for C {
    fn bump(&mut self) -> u32 {
        1
    }
}

impl<T: ?Sized + Counter> Counter for &mut T {
    fn bump(&mut self) -> u32 {
        (**self).bump()
    }
}

#[thrust_macros::ensures(result <= 100)]
fn g<T: Counter>(mut x: T) -> u32 {
    x.bump()
}

fn main() {
    let mut c = C;
    let d: &mut dyn Counter = &mut c;
    assert!(g::<&mut dyn Counter>(d) <= 100);
}

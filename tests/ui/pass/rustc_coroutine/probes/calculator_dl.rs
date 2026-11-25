//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120 THRUST_TRY_SPECS=1

// layout.rs's `LayoutCalculator<Cx>` reduced: its model is its one field's, so a contract names
// the data layout of `self.cx` as `Cx::dl_of(*self, dl)`, and a caller holding the calculator
// states it with its own `C::dl_of(*calc, dl)`.

use thrust_models::forall;

#[derive(Copy, Clone, PartialEq, Eq)]
pub struct TargetDataLayout {
    pub pointer_size: u64,
}

impl thrust_models::Model for TargetDataLayout {
    type Ty = Self;
}

#[thrust_macros::context]
pub trait HasDataLayout {
    #[thrust_macros::predicate]
    fn dl_of(self, dl: TargetDataLayout) -> bool;

    #[thrust_macros::ensures(Self::dl_of(*self, *result))]
    fn data_layout(&self) -> &TargetDataLayout;
}

#[thrust_macros::context]
impl HasDataLayout for TargetDataLayout {
    #[thrust_macros::predicate]
    fn dl_of(self, dl: TargetDataLayout) -> bool {
        self == dl
    }

    fn data_layout(&self) -> &TargetDataLayout {
        self
    }
}

#[thrust_macros::context]
impl HasDataLayout for &TargetDataLayout {
    #[thrust_macros::predicate]
    fn dl_of(self, dl: TargetDataLayout) -> bool {
        *self == dl
    }

    fn data_layout(&self) -> &TargetDataLayout {
        (**self).data_layout()
    }
}

pub struct LayoutCalculator<Cx> {
    pub cx: Cx,
}

impl<Cx: thrust_models::Model> thrust_models::Model for LayoutCalculator<Cx> {
    type Ty = <Cx as thrust_models::Model>::Ty;
}

#[thrust_macros::context]
impl<Cx: HasDataLayout> LayoutCalculator<Cx> {
    #[thrust_macros::requires(forall(|dl: TargetDataLayout| !Cx::dl_of(*self, dl) || dl.pointer_size == 8))]
    #[thrust_macros::ensures(result == 8)]
    fn pointer_size(&self) -> u64 {
        let dl = self.cx.data_layout();
        assert!(dl.pointer_size == 8);
        dl.pointer_size
    }
}

#[thrust_macros::requires(forall(|dl: TargetDataLayout| !C::dl_of(*calc, dl) || dl.pointer_size == 8))]
#[thrust_macros::ensures(result == 8)]
fn layout<C: HasDataLayout>(calc: &LayoutCalculator<C>) -> u64 {
    calc.pointer_size()
}

fn main() {
    let dl = TargetDataLayout { pointer_size: 8 };
    let calc = LayoutCalculator { cx: &dl };
    assert!(layout(&calc) == 8);
}

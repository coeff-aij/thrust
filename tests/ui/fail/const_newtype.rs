//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct ReprFlags(u32);

impl ReprFlags {
    pub const IS_C: ReprFlags = ReprFlags(1);
}

impl thrust_models::Model for ReprFlags {
    type Ty = Self;
}

fn is_c(f: ReprFlags) -> bool {
    f == ReprFlags::IS_C
}

fn main() {
    assert!(!is_c(ReprFlags::IS_C));
    assert!(is_c(ReprFlags(2)));
}

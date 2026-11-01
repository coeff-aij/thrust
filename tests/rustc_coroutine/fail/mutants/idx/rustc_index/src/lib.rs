pub mod bit_set;

mod idx;
mod slice;
mod vec;

pub use idx::{Idx, IntoSliceIdx};
pub use slice::IndexSlice;
pub use vec::IndexVec;

// The own iterators of rewrites.md R3 and R4, which rustc does not have.
pub use idx::IdxRange;
pub use slice::{IterEnumerated, SliceIter};

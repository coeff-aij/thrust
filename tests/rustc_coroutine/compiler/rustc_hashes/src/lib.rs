#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct Hash64 {
    inner: u64,
}

impl Hash64 {
    pub const ZERO: Hash64 = Hash64 { inner: 0 };

    #[inline]
    pub fn new(n: u64) -> Self {
        Self { inner: n }
    }

    #[inline]
    pub fn as_u64(self) -> u64 {
        self.inner
    }

    #[inline]
    #[thrust::trusted]
    #[thrust::callable]
    pub fn wrapping_add(self, other: Self) -> Self {
        Self {
            inner: self.inner.wrapping_add(other.inner),
        }
    }
}

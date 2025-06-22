use std::cmp::Ordering;
use std::ops::Range;

/// Range of virtual addresses
///
/// These are fully ordered by their beginning address so that it is easy to keep them sorted in
/// the MMU struct.
#[derive(Clone, Copy)]
pub struct AddrRange {
    pub start: usize,
    pub end: usize,
}

impl AddrRange {
    /// Create a new address range
    ///
    /// # Arguments
    /// - `addr`: First address in the range
    /// - `len`: Number of bytes in the address range
    #[must_use]
    pub fn new(addr: usize, len: usize) -> Self {
        Self {
            start: addr,
            end: addr + len,
        }
    }

    /// Checks for containment of the address
    #[must_use]
    #[inline]
    pub fn contains(&self, addr: usize) -> bool {
        self.start <= addr && addr < self.end
    }

    /// Compares this address range to a specific address.
    #[inline]
    pub fn compare_to_addr(&self, addr: usize) -> Ordering {
        if self.contains(addr) {
            Ordering::Equal
        } else if self.start >= addr {
            Ordering::Greater
        } else {
            Ordering::Less
        }
    }
}

impl std::fmt::Debug for AddrRange {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[0x{:016X} - 0x{:016X}]", self.start, self.end)
    }
}

impl From<Range<usize>> for AddrRange {
    fn from(value: Range<usize>) -> Self {
        Self {
            start: value.start,
            end: value.start,
        }
    }
}

impl PartialEq for AddrRange {
    fn eq(&self, other: &Self) -> bool {
        self.start == other.start
    }
}

impl Eq for AddrRange {}

impl PartialOrd for AddrRange {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.start.cmp(&other.start))
    }
}

impl Ord for AddrRange {
    fn cmp(&self, other: &Self) -> Ordering {
        self.start.cmp(&other.start)
    }
}

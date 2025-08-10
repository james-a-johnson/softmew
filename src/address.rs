use std::cmp::Ordering;
use std::ops::Range;

/// Range of virtual addresses
///
/// These are fully ordered by their beginning address so that it is easy to keep them sorted in
/// the MMU struct.
///
/// The start address is inclusive and the end address is exclusive.
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
    #[must_use]
    pub fn compare_to_addr(&self, addr: usize) -> Ordering {
        if self.contains(addr) {
            Ordering::Equal
        } else if self.start >= addr {
            Ordering::Greater
        } else {
            Ordering::Less
        }
    }

    /// Test for full equality between two address ranges.
    ///
    /// This is mainly just used for testing.
    pub fn full_eq(&self, other: &Self) -> bool {
        self.start == other.start && self.end == other.end
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
            end: value.end,
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ordering() {
        let a = AddrRange::new(0, 10);
        let b = AddrRange::new(1, 9);
        assert!(a < b);
        assert!(b > a);
    }
}

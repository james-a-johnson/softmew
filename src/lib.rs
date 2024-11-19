use crate::address::AddrRange;
pub use crate::map::Mapping;
pub use crate::fault::Fault;
use crate::fault::Reason;
use crate::map::Perm;

pub mod address;
pub mod map;
pub mod fault;

/// Software memory management unit
///
/// A full software implementation of a memory management unit with byte level permissions.
///
/// This MMU is meant to be as flexible as possible. It can map any amount of memory at any address
/// with no alignment requirements. The only limitation is that mapped address ranges may not
/// overlap each other.
///
/// The goal of this MMU is to be very performant for reads, writes, and resets. Memory can be
/// initialized up to some point and then snapshotted after initialization using clone. The copy
/// can then be used as the backing memory for something before using the snapshot to reset the
/// memory to the original state before starting a new run.
///
/// A snapshot of memory is literally just a full copy of memory at some point in time. This means
/// that memory usage will double if you take a snapshot of an MMU. This crate makes the choice of
/// sacrificing memory usage for runtime performance.
///
/// # Examples
/// ```
/// use softmew::MMU;
/// use softmew::map::Perm;
///
/// # fn use_mmu(_mew: &mut MMU) {}
///
/// let mut memory = MMU::new();
/// memory.map_memory(0x1000, 0x2000, Perm::default()).expect("Failed to map data section");
/// memory.map_memory(0x8000, 0x9000, Perm::READ | Perm::EXEC).expect("Failed to map code section");
///
/// let data = memory.get_mapping_mut(0x1000).expect("Failed to get data section");
/// // load data here
/// // data.data_mut().copy_from_slice(&rw_data);
/// let code = memory.get_mapping_mut(0x8000).expect("Failed to get code section");
/// // load code data here
/// // code.data_mut().copy_from_slice(&code_data);
///
/// // Make a snapshot
/// let snapshot = memory.clone();
///
/// // Use memory somehow
/// use_mmu(&mut memory);
///
/// // Reset memory
/// memory.reset(&snapshot);
/// ```
#[derive(Clone, Default)]
pub struct MMU {
    /// List of AddrRanges sorted by the lowest address in the range
    ///
    /// Must always remain sorted or else everything will break. It is assumed that an element at
    /// index `i` in pages is the address range for the backing memory at index `i` in data.
    pages: Vec<AddrRange>,
    /// List of the allocated memory to back each memory mapping
    ///
    /// This must always be sorted by the address at which the memory is mapped at. This will
    /// ensure that it is always sorted in the same way as pages.
    data: Vec<Mapping>,
}

impl MMU {
    /// Create a new memory management instance
    ///
    /// Will have no memory associated with it.
    #[must_use]
    pub fn new() -> Self {
        Self {
            pages: Vec::new(),
            data: Vec::new(),
        }
    }

    /// Get the mapping associated with an address
    ///
    /// Looks through all of the mapped memory to find any that contain `addr` and returns a
    /// reference to that mapping.
    ///
    /// If no mapping is found, None is returned.
    #[must_use]
    pub fn get_mapping(&self, addr: usize) -> Option<&Mapping> {
        debug_assert!(self.pages.is_sorted(), "Pages list is not sorted");
        debug_assert!(self.data.is_sorted_by(|d1, d2| d1.addr < d2.addr), "Memory mappings are not sorted");
        for (i, map) in self.pages.iter().enumerate() {
            if map.contains(addr) {
                return Some(unsafe { self.data.get_unchecked(i) })
            }
        }
        None
    }

    /// Get a mutable reference to the mapping associated with `addr`
    ///
    /// Same as [`MMU::get_mapping`] but will get a mutable reference.
    #[must_use]
    pub fn get_mapping_mut(&mut self, addr: usize) -> Option<&mut Mapping> {
        debug_assert!(self.pages.is_sorted(), "Pages list is not sorted");
        debug_assert!(self.data.is_sorted_by(|d1, d2| d1.addr < d2.addr), "Memory mappings are not sorted");
        for (i, map) in self.pages.iter().enumerate() {
            if map.contains(addr) {
                return Some(unsafe { self.data.get_unchecked_mut(i) })
            }
        }
        None
    }

    /// Create a new memory mapping of the address range [start, end) with the given permission
    ///
    /// # Errors
    /// Returns an error if any of the address ranges that are already mapped would overlap with
    /// the new mapping. Returns the address range of the first mapping found that would overlap
    /// with it.
    ///
    /// # Panics
    /// This function will panic if `end` <= `start`.
    pub fn map_memory(&mut self, start: usize, end: usize, perm: Perm) -> Result<(), AddrRange> {
        assert!(end > start, "Memory range is invalid");
        // Loop through to make sure there isn't any overlap
        for map in &self.pages {
            // See
            // https://stackoverflow.com/a/12888920
            if start.max(map.start) < end.min(map.end) {
                return Err(*map);
            }
        }
        let new_mapping = Mapping::new_perm(start, end - start, perm);
        let new_range = AddrRange::new(start, end - start);
        self.pages.push(new_range);
        self.data.push(new_mapping);
        self.pages.sort();
        self.data.sort_by(|m1, m2| m1.addr.cmp(&m2.addr));
        Ok(())
    }

    /// Reads some memory in this MMU's memory space
    ///
    /// This is a simple wrapper around finding the correct memory space using [`MMU::get_mapping`]
    /// and then calling [`Mapping::read_perm`] on the returned mapping.
    ///
    /// # Errors
    /// Returns an error if `addr` is not mapped in this MMU. Will also propagate the fault
    /// returned by the underlying [`Mapping`].
    pub fn read_perm(&self, addr: usize, buf: &mut [u8]) -> Result<(), Fault> {
        let map = self.get_mapping(addr).ok_or(Fault {
            address: addr..addr+buf.len(),
            reason: Reason::NotMapped,
        })?;
        map.read_perm(addr, buf)
    }

    /// Writes some memory in this MMU's memory space
    ///
    /// This is a simple wrapper around finding the correct memory space using
    /// [`MMU::get_mapping_mut`]
    /// and then calling [`Mapping::write_perm`] on the returned mapping.
    ///
    /// # Errors
    /// Returns an error if `addr` is not mapped in this MMU. Will also propagate the fault
    /// returned by the underlying [`Mapping`].
    pub fn write_perm(&mut self, addr: usize, buf: &[u8]) -> Result<(), Fault> {
        let map = self.get_mapping_mut(addr).ok_or(Fault {
            address: addr..addr+buf.len(),
            reason: Reason::NotMapped,
        })?;
        map.write_perm(addr, buf)
    }

    /// Fetches some memory for execution in this MMU's memory space
    ///
    /// This is a simple wrapper around finding the correct memory space using
    /// [`MMU::get_mapping`]
    /// and then calling [`Mapping::fetch_perm`] on the returned mapping.
    ///
    /// # Errors
    /// Returns an error if `addr` is not mapped in this MMU. Will also propagate the fault
    /// returned by the underlying [`Mapping`].
    pub fn fetch_perm(&mut self, addr: usize, buf: &mut [u8]) -> Result<(), Fault> {
        let map = self.get_mapping(addr).ok_or(Fault {
            address: addr..addr+buf.len(),
            reason: Reason::NotMapped,
        })?;
        map.fetch_perm(addr, buf)
    }

    /// Reset all memory to some snapshotted state
    ///
    /// Resets all of the memory in this MMU to the state that it was at when `original` was cloned
    /// from this MMU.
    ///
    /// # Panics
    /// May panic if `original` was not cloned from this MMU or if more more memory was mapped to
    /// `original` after it was cloned.
    pub fn reset(&mut self, original: &Self) {
        debug_assert_eq!(self.data.len(), original.data.len());
        for (dirty, orig) in self.data.iter_mut().zip(original.data.iter()) {
            if dirty.dirtied() {
                dirty.reset(orig);
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn overlapping() {
        let mut mew = MMU::new();
        let expected = AddrRange::new(0x100, 0x100);
        mew.map_memory(0x100, 0x200, Perm::default()).expect("Failed to map first memory region");

        // First byte overlaps
        let res = mew.map_memory(0x10, 0x101, Perm::default());
        let err = res.expect_err("Overlapping memory mapping succeeded");
        assert_eq!(err, expected);

        // Last byte overlaps
        let res = mew.map_memory(0x1ff, 0x201, Perm::default());
        let err = res.expect_err("Overlapping memory mapping succeeded");
        assert_eq!(err, expected);

        // New mapping completely contains old one
        let res = mew.map_memory(0x0, 0x1000, Perm::default());
        let err = res.expect_err("Overlapping memory mapping succeeded");
        assert_eq!(err, expected);

        // Old mapping completely contains new one
        let res = mew.map_memory(0x110, 0x120, Perm::default());
        let err = res.expect_err("Overlapping memory mapping succeeded");
        assert_eq!(err, expected);

        mew.map_memory(0x80, 0x100, Perm::default()).expect("Failed to map second memory region");
        mew.map_memory(0x200, 0x280, Perm::default()).expect("Failed to map third memory region");
    }

    #[test]
    fn get() {
        let mut mew = MMU::new();
        mew.map_memory(0x1000, 0x2000, Perm::default()).unwrap();
        mew.map_memory(0x8000, 0x9000, Perm::default()).unwrap();
        {
            let map = mew.get_mapping(0x1080).expect("Failed to get mapped memory");
            assert_eq!(map.addr, 0x1000, "Mapping did not have expected address of 0x1000");
        }
        {
            let map = mew.get_mapping(0x8080).expect("Failed to get mapped memory");
            assert_eq!(map.addr, 0x8000, "Mapping did not have expected address of 0x8000");
        }
        let res = mew.get_mapping(0x2000);
        assert!(res.is_none(), "Got mapping for invalid address");

        let res = mew.get_mapping(0x9000);
        assert!(res.is_none(), "Got mapping for invalid address");
    }
}

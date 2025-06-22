use crate::{address::AddrRange, fault::Reason, Fault, permission::Perm};

/// Specific memory range in a simple mapping.
/// 
/// Holds some amount of memory with all of it using the same memory permissions.
pub struct SimpleMap {
    addr: usize,
    perm: Perm,
    data: Box<[u8]>,
}

impl SimpleMap {
    /// Create a new mapping at the specified address with the given permissions and size.
    pub fn new(addr: usize, size: usize, perm: Perm) -> Self {
        let data = vec![0u8; size];
        Self {
            addr,
            perm,
            data: data.into_boxed_slice(),
        }
    }

    /// Read some data from the mapping.
    /// 
    /// # Errors
    /// - Not mapped error if the requested address is outside the contained memory range
    /// - Fault if the memory does not have read permissions
    pub fn read(&self, addr: usize, buf: &mut [u8]) -> Result<(), Fault> {
        if addr < self.addr {
            return Err(Fault {
                address: addr..addr+buf.len(),
                reason: Reason::NotMapped,
            });
        }
        let offset = addr - self.addr;
        if offset + buf.len() > self.data.len() {
            return Err(Fault {
                address: addr..addr+buf.len(),
                reason: Reason::NotMapped,
            });
        }
        if !self.perm.read() {
            return Err(Fault {
                address: addr..addr+buf.len(),
                reason: Reason::NotReadable,
            });
        }
        buf.copy_from_slice(&self.data[offset..][..buf.len()]);
        Ok(())
    }
    /// Write some data into the mapping.
    ///
    /// # Errors
    /// - Not mapped error if the requested address is outside the contained memory range
    /// - Fault if the memory does not have read permissions
    pub fn write(&mut self, addr: usize, buf: &[u8]) -> Result<(), Fault> {
        if addr < self.addr {
            return Err(Fault {
                address: addr..addr+buf.len(),
                reason: Reason::NotMapped,
            });
        }
        let offset = addr - self.addr;
        if offset + buf.len() > self.data.len() {
            return Err(Fault {
                address: addr..addr+buf.len(),
                reason: Reason::NotMapped,
            });
        }
        if !self.perm.write() {
            return Err(Fault {
                address: addr..buf.len(),
                reason: Reason::NotWritable,
            });
        }
        self.data[offset..][..buf.len()].copy_from_slice(buf);
        Ok(())
    }
}

impl AsRef<[u8]> for SimpleMap {
    fn as_ref(&self) -> &[u8] {
        self.data.as_ref()
    }
}

impl AsMut<[u8]> for SimpleMap {
    fn as_mut(&mut self) -> &mut [u8] {
        self.data.as_mut()
    }
}

/// Software memory management unit.
///
/// This implementation is more representative of an actual MMU and applies a specific memory
/// permission to an entire page. This implementation also does not support write before read
/// permission that can be used by [`crate::MMU`].
#[derive(Default)]
pub struct MMUSimple {
    /// List of AddrRanges sorted by the lowest address in the range
    ///
    /// Must always remain sorted or else everything will break. It is assumed that an element at
    /// index `i` in pages is the address range for the backing memory at index `i` in data.
    pages: Vec<AddrRange>,
    /// List of the allocated memory to back each memory mapping
    ///
    /// This must always be sorted by the address at which the memory is mapped at. This will
    /// ensure that it is always sorted in the same way as pages.
    data: Vec<SimpleMap>,
}

impl MMUSimple {
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

    /// Create a new memory mapping of the address range [start, size+1)
    ///
    /// # Errors
    /// Returns an error if any of the address ranges that are already mapped would overlap with
    /// the new mapping. Returns the address range of the first mapping found that would overlap
    /// with it.
    ///
    /// # Panics
    /// Panics if `size` is zero. This MMU does not support zero sized memory mappings.
    pub fn map_memory(&mut self, start: usize, size: usize, perm: Perm) -> Result<(), AddrRange> {
        assert!(size != 0, "Zero sized memory mappings are not supported");
        let end = start + size;
        // Loop through to make sure there isn't any overlap
        for map in &self.pages {
            // See
            // https://stackoverflow.com/a/12888920
            if start.max(map.start) < end.min(map.end) {
                return Err(*map);
            }
        }
        let new_range = AddrRange::new(start, size);
        let map = SimpleMap::new(start, size, perm);
        self.pages.push(new_range);
        self.data.push(map);
        self.pages.sort();
        self.data.sort_by(|m1, m2| m1.addr.cmp(&m2.addr));
        Ok(())
    }

    /// Get the mapping associated with an address
    ///
    /// Looks through all of the mapped memory to find any that contain `addr` and returns a
    /// reference to that mapping.
    ///
    /// If no mapping is found, None is returned.
    #[must_use]
    pub fn get_mapping(&self, addr: usize) -> Option<&SimpleMap> {
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
    /// Same as [`MMUSimple::get_mapping`] but will get a mutable reference.
    #[must_use]
    pub fn get_mapping_mut(&mut self, addr: usize) -> Option<&mut SimpleMap> {
        debug_assert!(self.pages.is_sorted(), "Pages list is not sorted");
        debug_assert!(self.data.is_sorted_by(|d1, d2| d1.addr < d2.addr), "Memory mappings are not sorted");
        for (i, map) in self.pages.iter().enumerate() {
            if map.contains(addr) {
                return Some(unsafe { self.data.get_unchecked_mut(i) })
            }
        }
        None
    }

    /// Reads some memory in this MMU's memory space
    ///
    /// This is a simple wrapper around finding the correct memory space using [`MMUSimple::get_mapping`]
    /// and then calling [`SimpleMap::read`] on the returned mapping.
    ///
    /// # Errors
    /// Returns an error if `addr` is not mapped in this MMU. Will also propagate the fault
    /// returned by the underlying [`Mapping`].
    pub fn read(&self, addr: usize, buf: &mut [u8]) -> Result<(), Fault> {
        let map = self.get_mapping(addr).ok_or(Fault {
            address: addr..addr+buf.len(),
            reason: Reason::NotMapped,
        })?;
        map.read(addr, buf)
    }

    /// Writes some memory in this MMU's memory space
    ///
    /// This is a simple wrapper around finding the correct memory space using
    /// [`MMUSimple::get_mapping_mut`]
    /// and then calling [`SimpleMap::write`] on the returned mapping.
    ///
    /// # Errors
    /// Returns an error if `addr` is not mapped in this MMU. Will also propagate the fault
    /// returned by the underlying [`Mapping`].
    pub fn write(&mut self, addr: usize, buf: &[u8]) -> Result<(), Fault> {
        let map = self.get_mapping_mut(addr).ok_or(Fault {
            address: addr..addr+buf.len(),
            reason: Reason::NotMapped,
        })?;
        map.write(addr, buf)
    }
}

use crate::fault::{Fault, Reason};
use crate::permission::Perm;
use std::fmt::{Debug, Formatter};
use std::ops::Range;

/// This will control the size of a dirty block
///
/// Resetting works on blocks of memory and this controls that block size. Every time a write
/// happens, the map will keep track of which blocks have been dirtied. Then on a reset every block
/// will be reset to the original data. A write of any size to a block will dirty it so this
/// parameter can change the performance of resetting a lot.
///
/// A large value for this means that only a few expensive memcopies will need to be made. A
/// smaller value means a lot more cheap memcopies will be made.
const PAGE_SIZE: usize = 64;

/// Memory mapping with byte level permissions
///
/// Software level mmapped page essentially. Has an array of data and an array of permissions for
/// each byte.
///
/// When accessing memory with any of [`Mapping::read_perm`], [`Mapping::write_perm`], or
/// [`Mapping::fetch_perm`], the permissions for each byte that is accessed will be checked.
///
/// [`Mapping::data`] and [`Mapping::data_mut`] allow for access to the backing buffer of data as a
/// plain slice of bytes.
pub struct Mapping {
    data: Box<[u8]>,
    perms: Box<[Perm]>,
    dirty: Vec<usize>,
    dirty_flag: Box<[u64]>,
    pub addr: usize,
}

impl Debug for Mapping {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Mapping ({:08X}, {:08X})",
            self.addr,
            self.addr + self.data.len()
        )
    }
}

impl Mapping {
    /// Create a new mapping for address `addr` of `len` bytes.
    ///
    /// Default permissions for all of the bytes will be [`Perm::READ`] and [`Perm::WRITE`].
    /// All bytes will be initialized to the value 0.
    #[must_use]
    #[inline]
    pub fn new(addr: usize, len: usize) -> Self {
        Self::new_perm(addr, len, Perm::default())
    }

    /// Same as the function [`Mapping::new`] but will set all of the permission values to
    /// `perm`.
    #[must_use]
    pub fn new_perm(addr: usize, len: usize, perm: Perm) -> Self {
        let dirty_len = (len / PAGE_SIZE) + 1;
        let dirty_flag_len = (len / PAGE_SIZE / 64) + 1;
        let mut data = Vec::with_capacity(len);
        let mut perms = Vec::with_capacity(len);
        let dirty = Vec::with_capacity(dirty_len);
        let mut dirty_flag = Vec::with_capacity(dirty_flag_len);
        // SAFETY: All of these vectors have the correct capacity set and any data will already in
        // the backing memory is a valid representation of an u8 or u64 or usize. Additionally,
        // all of this vectors will be immediately initialized afterward to be filled with correct
        // default data.
        unsafe {
            data.set_len(len);
            perms.set_len(len);
            dirty_flag.set_len(dirty_flag_len);
        }
        data[..].fill(0);
        perms[..].fill(perm);
        dirty_flag[..].fill(0);
        Self {
            data: data.into_boxed_slice(),
            perms: perms.into_boxed_slice(),
            dirty,
            dirty_flag: dirty_flag.into_boxed_slice(),
            addr,
        }
    }

    /// Access the backing array of data
    #[must_use]
    pub fn data(&self) -> &[u8] {
        &self.data
    }

    /// Get a mutable reference to the backing array of data
    #[must_use]
    pub fn data_mut(&mut self) -> &mut [u8] {
        &mut self.data
    }

    /// Range of addresses mapped by memory
    #[must_use]
    pub fn range(&self) -> Range<usize> {
        self.addr..self.addr + self.data.len()
    }

    #[must_use]
    pub fn set_perms(&mut self, addrs: Range<usize>, perm: Perm) -> Option<()> {
        self.perms.get_mut(addrs).map(|p| p.fill(perm))
    }

    /// Check that some address range is properly contained by this mapping and has the correct
    /// permissions.
    ///
    /// If all checks pass, this function will return a range that can be used to index the data
    /// contained by this struct to access the requested addresses.
    ///
    /// # Errors
    /// Returns an error if any address goes out of range of this mapping or the required
    /// permissions are not met.
    fn check_perm(&self, addrs: Range<usize>, perm: Perm) -> Result<Range<usize>, Fault> {
        if addrs.start < self.addr {
            return Err(Fault {
                address: addrs.clone(),
                reason: Reason::NotMapped,
            });
        }
        let offset_range = (addrs.start - self.addr)..(addrs.end - self.addr);
        if offset_range.end > self.data.len() {
            return Err(Fault {
                address: addrs.clone(),
                reason: Reason::NotMapped,
            });
        }
        // SAFETY: The perms vector is kept in sync with the data range. Above, we've checked that it
        // is a valid range for the data vector. So we can safely use it here to index into the
        // permissions vector.
        let perms = unsafe { self.perms.get_unchecked(offset_range.clone()) };
        if !perms.iter().all(|p| *p & perm == perm) {
            return Err(Fault {
                address: addrs.clone(),
                reason: perm.into(),
            });
        }
        Ok(offset_range)
    }

    fn check_perm_write(
        &self,
        addrs: Range<usize>,
        perm: Perm,
    ) -> Result<(Range<usize>, bool), Fault> {
        if addrs.start < self.addr {
            return Err(Fault {
                address: addrs.clone(),
                reason: Reason::NotMapped,
            });
        }
        let offset_range = (addrs.start - self.addr)..(addrs.end - self.addr);
        if offset_range.end > self.data.len() {
            return Err(Fault {
                address: addrs.clone(),
                reason: Reason::NotMapped,
            });
        }
        // SAFETY: See the safety comment from check_perm
        let perms = unsafe { self.perms.get_unchecked(offset_range.clone()) };
        let mut write = Perm::WRITE;
        let mut raw = Perm::NONE;
        for p in perms {
            write &= *p;
            raw |= *p;
            if !write.write() {
                break;
            }
        }
        if !write.write() {
            return Err(Fault {
                address: addrs.clone(),
                reason: perm.into(),
            });
        }
        Ok((offset_range, raw.raw()))
    }

    /// Take a snapshot of the current state of the mapping
    ///
    /// Returns a copy of all of the memory and permissions. This is essentially just a clone but
    /// will clear all of the dirty state tracking.
    #[must_use]
    pub fn snapshot(&mut self) -> Self {
        self.dirty.clear();
        self.dirty_flag[..].fill(0);
        let data = self.data.clone();
        let perms = self.perms.clone();
        let dirty = Vec::with_capacity(self.dirty.capacity());
        let dirty_flag = self.dirty_flag.clone();
        Self {
            data,
            perms,
            dirty,
            dirty_flag,
            addr: self.addr,
        }
    }

    /// Read memory with permission checks
    ///
    /// # Arguments
    /// - `addr`: Address of data to be accessed. Should be contained by [`Mapping::range`]
    /// - `buf`: Buffer to read data into
    ///
    /// # Panic
    /// This function assumes that `addr` is a valid address for this mapping. If it is not then a
    /// panic will occur due to an out of bound access or the creation of an invalid range.
    ///
    /// # Errors
    /// If the address read range goes out of bounds or any byte does not have [`Perm::READ`] set,
    /// then a fault will occur and an error will return.
    ///
    /// In the case of an error, no bytes of `buf` will be written and it will be left the same
    /// value as when it was passed to the function.
    pub fn read_perm(&self, addr: usize, buf: &mut [u8]) -> Result<(), Fault> {
        let offset = self.check_perm(addr..addr + buf.len(), Perm::READ)?;
        // SAFETY: check_perm will return a valid range to index into the data array.
        let accessed_data = unsafe { self.data.get_unchecked(offset) };
        buf.copy_from_slice(accessed_data);
        Ok(())
    }

    /// Write memory with permission checks
    ///
    /// Any of the bytes that were written that have [`Perm::RAW`] set will gain the [`Perm::READ`]
    /// permission.
    ///
    /// # Arguments
    /// - `addr`: Address of data to be written. Should be contained by [`Mapping::range`]
    /// - `buf`: Data to write to accessed memory
    ///
    /// # Panic
    /// This function assumes that `addr` is a valid address for this mapping. If it is not then a
    /// panic will occur due to an out of bound access or the creation of an invalid range.
    ///
    /// # Errors
    /// If the address read range goes out of bounds or any byte does not have [`Perm::WRITE`] set,
    /// then a fault will occur and an error will return.
    ///
    /// In the case of an error, no bytes of `buf` will be written and it will be left the same
    /// value as when it was passed to the function.
    pub fn write_perm(&mut self, addr: usize, buf: &[u8]) -> Result<(), Fault> {
        let (offset, has_raw) = self.check_perm_write(addr..addr + buf.len(), Perm::WRITE)?;
        // SAFETY: check_perm_write will return a range that is safe to index into the data vector.
        let accessed_data = unsafe { self.data.get_unchecked_mut(offset.clone()) };
        accessed_data.copy_from_slice(buf);
        // Optimize and assume that if any of the bytes have RAW set then all of them have RAW set
        if has_raw {
            // SAFETY: The offset range is safe for the data vector. Since the perms and data vector
            // always have the same shape, it is safe to use it to index into the perms array.
            let perms_to_set = unsafe { self.perms.get_unchecked_mut(offset.clone()) };
            for p in perms_to_set {
                *p |= Perm::READ;
            }
        }
        let start_block = offset.start / PAGE_SIZE;
        let end_block = offset.end / PAGE_SIZE;
        for block in start_block..=end_block {
            let idx = block / 64;
            let bit = block % 64;
            if self.dirty_flag[idx] & (1 << bit) == 0 {
                self.dirty.push(block);
                self.dirty_flag[idx] |= 1 << bit;
            }
        }
        Ok(())
    }

    /// Fetch memory for execution with permission checks
    ///
    /// This is exactly the same as [`Mapping::read_perm`] but it is checking for [`Perm::EXEC`] on
    /// every byte.
    ///
    /// # Errors
    /// Same as [`Mapping::read_perm`]
    pub fn fetch_perm(&self, addr: usize, buf: &mut [u8]) -> Result<(), Fault> {
        let offset = self.check_perm(addr..addr + buf.len(), Perm::EXEC)?;
        // SAFETY: check_perm returns a valid index for the data vector.
        let accessed_data = unsafe { self.data.get_unchecked(offset) };
        buf.copy_from_slice(accessed_data);
        Ok(())
    }

    /// Reset a memory mapping to have the same values as a snapshotted state
    ///
    /// This function assumes that the snapshot state has not changed since it was cloned from.
    ///
    /// # Safety
    /// This function requires that `original` is a mapping that comes from snapshotting this
    /// mapping.
    ///
    /// # Panics
    /// If `original` is not a clone of this mapping then this may panic.
    pub(crate) unsafe fn reset(&mut self, original: &Self) {
        // Memory may not be a multiple of the page size. Need to make sure we don't address past
        // the end of the last page.
        let max_addr = self.data.len();
        for block in &self.dirty {
            let start = block * PAGE_SIZE;
            let end = max_addr.min((block + 1) * PAGE_SIZE);

            // SAFETY: This function is unsafe because it requries that original is a snapshot
            // of this memory mapping. Knowing that information, all of these ranges will have
            // been made by accesses to this memory which will make the indexing valid.

            // Copy data over
            let my_data = unsafe { self.data.get_unchecked_mut(start..end) };
            let orig_data = unsafe { original.data.get_unchecked(start..end) };
            my_data.copy_from_slice(orig_data);

            // Copy perms over
            let my_perms = unsafe { self.perms.get_unchecked_mut(start..end) };
            let orig_perms = unsafe { original.perms.get_unchecked(start..end) };
            my_perms.copy_from_slice(orig_perms);
            unsafe {
                *self.dirty_flag.get_unchecked_mut(block / 64) = 0;
            }
        }
        self.dirty.clear();
    }

    /// True if this mapping has been written to
    ///
    /// Tracks if this memory mapping has been written to since the last reset. A mapping will keep
    /// track of writes to its backing memory to increase the rate at which it can return to a
    /// snapshotted state.
    #[must_use]
    pub(crate) fn dirtied(&self) -> bool {
        !self.dirty.is_empty()
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn reset() {
        let mut map = Mapping::new(0x9e, 0x4999);
        let data = b"qwerty";
        let data2 = b"dvorak";
        let data3 = b"123456";
        map.write_perm(0x10f, data).expect("Failed first write");
        map.write_perm(0x409e, data).expect("Failed second write");
        let snapshot = map.snapshot();
        map.write_perm(0x10f, data2)
            .expect("Failed first overwrite");
        map.write_perm(0x409e, data3)
            .expect("Failed second overwrite");
        // SAFETY: snapshot is a snapshot of map so it's safe to use here.
        unsafe {
            map.reset(&snapshot);
        }
        let mut buffer = [0u8; 6];
        map.read_perm(0x10f, &mut buffer)
            .expect("Failed first read");
        assert_eq!(&buffer[..], data);
        map.read_perm(0x409e, &mut buffer)
            .expect("Failed second read");
        assert_eq!(&buffer[..], data);
    }

    #[test]
    fn read() {
        let mut map = Mapping::new(0x100, 0x100);
        {
            let data = map.data_mut();
            for i in 0..5 {
                data[i] = b"hello"[i];
            }
        }
        let mut buffer = [0u8; 10];
        map.read_perm(0x100, &mut buffer)
            .expect("Failed to read data");
        assert_eq!(&buffer, b"hello\x00\x00\x00\x00\x00");
    }

    #[test]
    fn write() {
        let mut map = Mapping::new(0x100, 0x100);
        map.write_perm(0x100, b"hello")
            .expect("Failed to write data");
        assert_eq!(&map.data[0..10], b"hello\x00\x00\x00\x00\x00");
    }

    #[test]
    fn raw() {
        let mut map = Mapping::new_perm(0x100, 0x100, Perm::RAW | Perm::WRITE);
        map.write_perm(0x105, b"hello")
            .expect("Failed to write data");
        let mut data = [0u8; 5];
        map.read_perm(0x105, &mut data)
            .expect("Failed to read RAW mapped data");
        assert_eq!(&data[..], b"hello");
    }

    #[test]
    fn fetch() {
        let mut map = Mapping::new_perm(0x100, 0x100, Perm::EXEC);
        {
            let data = map.data_mut();
            data[10..21].copy_from_slice(b"instruction");
        }
        let mut buffer = [0u8; 11];
        map.fetch_perm(0x10a, &mut buffer)
            .expect("Failed to fetch instruction data");
        assert_eq!(&buffer[..], b"instruction");
    }

    #[test]
    fn read_fail() {
        let map = Mapping::new_perm(0x100, 0x100, Perm::EXEC);
        let mut buffer = [0u8; 0x10];
        let res = map.read_perm(0x110, &mut buffer);
        assert!(res.is_err());
        let res = res.unwrap_err();
        let Fault { address, reason } = res;
        assert_eq!(address, 0x110..0x120);
        assert_eq!(reason, Reason::NotReadable);
    }

    #[test]
    fn write_fail() {
        let mut map = Mapping::new_perm(0x100, 0x100, Perm::EXEC);
        let buffer = [10u8; 0x10];
        let res = map.write_perm(0x110, &buffer);
        assert!(res.is_err());
        let res = res.unwrap_err();
        let Fault { address, reason } = res;
        assert_eq!(address, 0x110..0x120);
        assert_eq!(reason, Reason::NotWritable);
    }

    #[test]
    fn exec_fail() {
        let map = Mapping::new_perm(0x100, 0x100, Perm::READ);
        let mut buffer = [0u8; 0x10];
        let res = map.fetch_perm(0x110, &mut buffer);
        assert!(res.is_err());
        let res = res.unwrap_err();
        let Fault { address, reason } = res;
        assert_eq!(address, 0x110..0x120);
        assert_eq!(reason, Reason::NotExecutable);
    }

    #[test]
    fn not_mapped() {
        let mut map = Mapping::new_perm(0x100, 0x10, Perm::READ);
        let buffer = [0u8; 0x20];
        let res = map.write_perm(0x100, &buffer);
        assert!(res.is_err());
        let res = res.unwrap_err();
        let Fault { address, reason } = res;
        assert_eq!(address, 0x100..0x120);
        assert_eq!(reason, Reason::NotMapped);
    }
}

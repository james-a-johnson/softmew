use std::ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, Range};
use crate::fault::{Fault, Reason};

const PAGE_SIZE: usize = 4096;

/// Byte level memory permission
///
/// Represents how a specific byte of memory may be accessed. Can be any combination of
/// - [`Perm::NONE`]
/// - [`Perm::READ`]
/// - [`Perm::WRITE`]
/// - [`Perm::EXEC`]
/// - [`Perm::RAW`]
///
/// A combination can be made by oring together any two permissions to get the union of
/// those permissions.
///
/// You can create a default permission. That is just set as readable and writable currently.
///
/// The default value is currently `Perm::READ | Perm::WRITE`.
///
/// # NOTE
/// Any combination of permissions is allowed. You can set memory as being write only and
/// that memory will be write only. Any attempt to read or execute from that memory will
/// cause a fault.
///
/// Additionally, execute only memory is not readable. Any attempt to read it that isn't
/// an instruction fetch (via [`Mapping::fetch_perm`]) will cause a fault.
#[repr(transparent)]
#[derive(Clone, Copy, Eq, PartialEq)]
pub struct Perm(u8);

impl Perm {
    /// Memory may not be read, written, or executed
    pub const NONE: Self = Self(0);
    /// Memory may be read
    pub const READ: Self = Self(1 << 0);
    /// Memory may be written to
    pub const WRITE: Self = Self(1 << 1);
    /// Memory may be executed / fetched for execution
    pub const EXEC: Self = Self(1 << 2);
    /// Memory may be read after it has first been written to
    ///
    /// Makes sense to set this flag for uninitialized memory.
    pub const RAW: Self = Self(1 << 3);

    /// Check if permission allows reading
    #[must_use]
    pub fn read(&self) -> bool {
        *self & Self::READ == Self::READ
    }

    /// Check if permission allows writing
    #[must_use]
    pub fn write(&self) -> bool {
        *self & Self::WRITE == Self::WRITE
    }

    /// Check if permission allows for executing
    #[must_use]
    pub fn exec(&self) -> bool {
        *self & Self::EXEC == Self::EXEC
    }

    /// Check if read permission should be set after a write
    #[must_use]
    pub fn raw(&self) -> bool {
        *self & Self::RAW == Self::RAW
    }
}

impl Default for Perm {
    fn default() -> Self {
        Perm::READ | Perm::WRITE
    }
}

impl BitOr for Perm {
    type Output = Self;
    fn bitor(self, rhs: Self) -> Self::Output {
        Self(self.0 | rhs.0)
    }
}

impl BitOrAssign for Perm {
    fn bitor_assign(&mut self, rhs: Self) {
        self.0 |= rhs.0;
    }
}

impl BitAnd for Perm {
    type Output = Self;
    fn bitand(self, rhs: Self) -> Self::Output {
        Self(self.0 & rhs.0)
    }
}

impl BitAndAssign for Perm {
    fn bitand_assign(&mut self, rhs: Self) {
        self.0 &= rhs.0;
    }
}

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
#[derive(Clone)]
pub struct Mapping {
    data: Vec<u8>,
    perms: Vec<Perm>,
    dirty: Vec<usize>,
    dirty_flag: Vec<u64>,
    pub addr: usize,
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
        unsafe {
            data.set_len(len);
            perms.set_len(len);
            dirty_flag.set_len(dirty_flag_len);
        }
        data[..].fill(0);
        perms[..].fill(perm);
        dirty_flag[..].fill(0);
        Self { data, perms, dirty, dirty_flag, addr }
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
    /// This function makes one assumption which is that the first address of the range is properly
    /// contained by this mapping. No other assumptions are made and all other checks will be made.
    ///
    /// If all checks pass, this function will return a range that can be used to index the data
    /// contained by this struct to access the requested addresses.
    ///
    /// # Errors
    /// Returns an error if any address goes out of range of this mapping or the required
    /// permissions are not met.
    fn check_perm(&self, addrs: Range<usize>, perm: Perm) -> Result<Range<usize>, Fault> {
        let offset_range = (addrs.start - self.addr)..(addrs.end - self.addr);
        if offset_range.end > self.data.len() {
            return Err(Fault {
                address: addrs.clone(),
                reason: Reason::NotMapped,
            });
        }
        let perms = unsafe {
            self.perms.get_unchecked(offset_range.clone())
        };
        if !perms.iter().all(|p| *p & perm != Perm::NONE) {
            return Err(Fault {
                address: addrs.clone(),
                reason: perm.into(),
            });
        }
        Ok(offset_range)
    }

    fn check_perm_write(&self, addrs: Range<usize>, perm: Perm) -> Result<(Range<usize>, bool), Fault> {
        let offset_range = (addrs.start - self.addr)..(addrs.end - self.addr);
        if offset_range.end > self.data.len() {
            return Err(Fault {
                address: addrs.clone(),
                reason: Reason::NotMapped,
            });
        }
        let perms = unsafe {
            self.perms.get_unchecked(offset_range.clone())
        };
        let mut write = Perm::WRITE;
        let mut raw = Perm::NONE;
        for p in perms {
            write &= *p;
            raw |= *p;
            if !write.write() { break; }
        }
        if !write.write() {
            return Err(Fault {
                address: addrs.clone(),
                reason: perm.into(),
            });
        }
        Ok((offset_range, raw.raw()))
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
        let offset = self.check_perm(addr..addr+buf.len(), Perm::READ)?;
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
        let (offset, has_raw) = self.check_perm_write(addr..addr+buf.len(), Perm::WRITE)?;
        let accessed_data = unsafe { self.data.get_unchecked_mut(offset.clone()) };
        accessed_data.copy_from_slice(buf);
        // Optimize and assume that if any of the bytes have RAW set then all of them have RAW set
        if has_raw {
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
        let offset = self.check_perm(addr..addr+buf.len(), Perm::EXEC)?;
        let accessed_data = unsafe { self.data.get_unchecked(offset) };
        buf.copy_from_slice(accessed_data);
        Ok(())
    }

    /// Reset a memory mapping to have the same values as a snapshotted state
    ///
    /// This function assumes that the snapshot state has not changed since it was cloned from.
    ///
    /// # Panics
    /// If `original` is not a clone of this mapping then this may panic.
    pub fn reset(&mut self, original: &Self) {
        // Memory may not be a multiple of the page size. Need to make sure we don't address past
        // the end of the last page.
        let max_addr = self.data.len();
        for block in &self.dirty {
            let start = block * PAGE_SIZE;
            let end = max_addr.min((block + 1) * PAGE_SIZE);
            self.data[start..end].copy_from_slice(&original.data[start..end]);
            self.perms[start..end].copy_from_slice(&original.perms[start..end]);
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
    pub fn dirtied(&self) -> bool {
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
        let snapshot = map.clone();
        map.write_perm(0x10f, data2).expect("Failed first overwrite");
        map.write_perm(0x409e, data3).expect("Failed second overwrite");
        map.reset(&snapshot);
        let mut buffer = [0u8; 6];
        map.read_perm(0x10f, &mut buffer).expect("Failed first read");
        assert_eq!(&buffer[..], data);
        map.read_perm(0x409e, &mut buffer).expect("Failed second read");
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
        map.read_perm(0x100, &mut buffer).expect("Failed to read data");
        assert_eq!(&buffer, b"hello\x00\x00\x00\x00\x00");
    }

    #[test]
    fn write() {
        let mut map = Mapping::new(0x100, 0x100);
        map.write_perm(0x100, b"hello").expect("Failed to write data");
        assert_eq!(&map.data[0..10], b"hello\x00\x00\x00\x00\x00");
    }

    #[test]
    fn raw() {
        let mut map = Mapping::new_perm(0x100, 0x100, Perm::RAW | Perm::WRITE);
        map.write_perm(0x105, b"hello").expect("Failed to write data");
        let mut data = [0u8; 5];
        map.read_perm(0x105, &mut data).expect("Failed to read RAW mapped data");
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
        map.fetch_perm(0x10a, &mut buffer).expect("Failed to fetch instruction data");
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

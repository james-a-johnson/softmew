use crate::permission::Perm;
use crate::address::AddrRange;
use std::error::Error;
use std::fmt::Display;

/// Memory fault
///
/// This will be returned when some error happens when reading memory.
#[derive(Clone)]
pub struct Fault {
    /// The addresses that were being accessed
    ///
    /// This is a range of the virtual addresses of the MMU that were being accessed.
    pub address: AddrRange,
    /// Reason the fault occurred
    ///
    /// Type of memory fault that occurred.
    pub reason: Reason,
}

impl Error for Fault {}

/// Types of memory faults
///
/// # NOTE
/// This does implement [`From`] for [`Perm`]. This is really only intended for
/// internal purposes. It may panic depending on what value the permission has when you try to
/// convert it. From is only implement for [`Perm::READ`], [`Perm::WRITE`], and [`Perm::EXEC`]. Any
/// other value for the permission will cause a panic.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Reason {
    /// Some part of the address range was not mapped
    NotMapped,
    /// Some part of the address range was not readable during a read
    NotReadable,
    /// Some part of the address range was not writable during a write
    NotWritable,
    /// Some part of the address range was not executable during a fetch
    NotExecutable,
}

impl From<Perm> for Reason {
    fn from(value: Perm) -> Self {
        match value {
            Perm::READ => Self::NotReadable,
            Perm::WRITE => Self::NotWritable,
            Perm::EXEC => Self::NotExecutable,
            _ => panic!("Encountered unexpected permission"),
        }
    }
}

impl std::fmt::Debug for Fault {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Failed to read 0x{:016X}..0x{:016X} reason: {}",
            self.address.start, self.address.end, self.reason
        )
    }
}

impl Display for Fault {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}-{}: {}",
            self.address.start, self.address.end, self.reason
        )
    }
}

impl Display for Reason {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match *self {
            Reason::NotMapped => write!(f, "Memory range is not mapped"),
            Reason::NotReadable => write!(f, "Memory range does not have read permission"),
            Reason::NotWritable => write!(f, "Memory range does not have write permission"),
            Reason::NotExecutable => write!(f, "Memory range does not have executable permission"),
        }
    }
}

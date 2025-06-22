use std::fmt::Display;
use std::ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign};

/// Access permissions for some amount of memory
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
/// # RAW Permission
/// A special RAW permission is included here as a way to detect uninitialized memory accesses.
/// RAW stands for Read After Write. Any memory that has that permission set will gain the read
/// permission when it is written to.
///
/// When using RAW you should not use [`Perm::READ`] as well on the memory or else it will have
/// no affect. The read permission means that it is safe to read the memory at any point during
/// execution. So a read to that memory before it has been initialized will not cause a fault.
///
/// # NOTE
/// Any combination of permissions is allowed. You can set memory as being write only and
/// that memory will be write only. Any attempt to read or execute from that memory will
/// cause a fault.
///
/// Additionally, execute only memory is not readable. Any attempt to read it  will cause a fault.
#[repr(transparent)]
#[derive(Clone, Copy, Eq, PartialEq, Debug)]
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

impl Display for Perm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.read() {
            write!(f, "R")?;
        } else {
            write!(f, "_")?;
        }
        
        if self.write() {
            write!(f, "W")?;
        } else {
            write!(f, "_")?;
        }
        
        if self.exec() {
            write!(f, "X")?;
        } else {
            write!(f, "_")?;
        }
        
        if self.raw() {
            write!(f, "U")
        } else {
            write!(f, "_")
        }
    }
}

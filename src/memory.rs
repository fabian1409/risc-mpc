use crate::{
    error::{Error, Result},
    Value,
};
use std::collections::HashMap;

/// Number of bytes per [`u64`].
pub const U64_BYTES: u64 = 8;

pub type Address = u64;

/// [`Memory`] used by riscMPC VM
#[derive(Default, Debug)]
pub struct Memory {
    memory: HashMap<Address, Value>,
}

impl Memory {
    pub fn new() -> Memory {
        Memory::default()
    }

    /// Loads the [`Value`] from the given [`Address`].
    pub fn load(&mut self, address: Address) -> Result<Value> {
        if address % U64_BYTES == 0 {
            let value = self.memory.entry(address).or_default();
            Ok(*value)
        } else {
            Err(Error::AddressNotAligned(address))
        }
    }

    /// Stores the [`Value`] at the given [`Address`].
    pub fn store(&mut self, address: Address, value: Value) -> Result<()> {
        if address % U64_BYTES == 0 {
            self.memory.insert(address, value);
            Ok(())
        } else {
            Err(Error::AddressNotAligned(address))
        }
    }
}

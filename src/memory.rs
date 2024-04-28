use crate::{
    error::{Error, Result},
    types::Value,
};
use intmap::IntMap;

/// Number of bytes per [`u64`].
pub const U64_BYTES: u64 = 8;

pub type Address = u64;

/// [`Memory`] used by riscMPC VM
#[derive(Default, Debug)]
pub struct Memory {
    memory: IntMap<Value>,
}

impl Memory {
    pub fn new() -> Memory {
        Memory::default()
    }

    /// Loads the [`Value`] from the given [`Address`].
    pub fn load(&self, address: Address) -> Result<Value> {
        if address % U64_BYTES == 0 {
            if let Some(value) = self.memory.get(address) {
                Ok(*value)
            } else {
                Ok(Value::default())
            }
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

use crate::{error::Error, Value};
use serde::{Deserialize, Serialize};
use std::{fmt::Display, str::FromStr};

/// Number of integer registers
const NUM_REGISTERS: usize = 32;

/// [`Register`] type to represent the 32 base registers of RISC-V.
#[allow(non_camel_case_types)]
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Register {
    x0,
    x1,
    x2,
    x3,
    x4,
    x5,
    x6,
    x7,
    x8,
    x9,
    x10,
    x11,
    x12,
    x13,
    x14,
    x15,
    x16,
    x17,
    x18,
    x19,
    x20,
    x21,
    x22,
    x23,
    x24,
    x25,
    x26,
    x27,
    x28,
    x29,
    x30,
    x31,
}

impl FromStr for Register {
    type Err = Error;

    fn from_str(s: &str) -> std::result::Result<Self, Self::Err> {
        match s {
            "x0" | "zero" => Ok(Self::x0),
            "x1" | "ra" => Ok(Self::x1),
            "x2" | "sp" => Ok(Self::x2),
            "x3" | "gp" => Ok(Self::x3),
            "x4" | "tp" => Ok(Self::x4),
            "x5" | "t0" => Ok(Self::x5),
            "x6" | "t1" => Ok(Self::x6),
            "x7" | "t2" => Ok(Self::x7),
            "x8" | "s0" | "fp" => Ok(Self::x8),
            "x9" | "s1" => Ok(Self::x9),
            "x10" | "a0" => Ok(Self::x10),
            "x11" | "a1" => Ok(Self::x11),
            "x12" | "a2" => Ok(Self::x12),
            "x13" | "a3" => Ok(Self::x13),
            "x14" | "a4" => Ok(Self::x14),
            "x15" | "a5" => Ok(Self::x15),
            "x16" | "a6" => Ok(Self::x16),
            "x17" | "a7" => Ok(Self::x17),
            "x18" | "s2" => Ok(Self::x18),
            "x19" | "s3" => Ok(Self::x19),
            "x20" | "s4" => Ok(Self::x20),
            "x21" | "s5" => Ok(Self::x21),
            "x22" | "s6" => Ok(Self::x22),
            "x23" | "s7" => Ok(Self::x23),
            "x24" | "s8" => Ok(Self::x24),
            "x25" | "s9" => Ok(Self::x25),
            "x26" | "s10" => Ok(Self::x26),
            "x27" | "s11" => Ok(Self::x27),
            "x28" | "t3" => Ok(Self::x28),
            "x29" | "t4" => Ok(Self::x29),
            "x30" | "t5" => Ok(Self::x30),
            "x31" | "t6" => Ok(Self::x31),
            _ => Err(Error::ParseRegisterError(s.to_owned())),
        }
    }
}

impl Display for Register {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let name = match self {
            Register::x0 => "zero",
            Register::x1 => "ra",
            Register::x2 => "sp",
            Register::x3 => "gp",
            Register::x4 => "tp",
            Register::x5 => "t0",
            Register::x6 => "t1",
            Register::x7 => "t2",
            Register::x8 => "s0",
            Register::x9 => "s1",
            Register::x10 => "a0",
            Register::x11 => "a1",
            Register::x12 => "a2",
            Register::x13 => "a3",
            Register::x14 => "a4",
            Register::x15 => "a5",
            Register::x16 => "a6",
            Register::x17 => "a7",
            Register::x18 => "s2",
            Register::x19 => "s3",
            Register::x20 => "s4",
            Register::x21 => "s5",
            Register::x22 => "s6",
            Register::x23 => "s7",
            Register::x24 => "s8",
            Register::x25 => "s9",
            Register::x26 => "s10",
            Register::x27 => "s11",
            Register::x28 => "t3",
            Register::x29 => "t4",
            Register::x30 => "t5",
            Register::x31 => "t6",
        };
        write!(f, "{name}")
    }
}

/// [`Registers`] holds all register values.
#[derive(Default, Debug)]
pub struct Registers {
    registers: [Value; NUM_REGISTERS],
}

impl Registers {
    /// Create all registers with `x0` and `x2(sp)` initialized.
    pub fn new() -> Registers {
        let mut registers = [Value::default(); NUM_REGISTERS];
        // init stack pointer to 8-byte aligned address
        registers[Register::x2 as usize] = Value::Public(0xffff_ffff_ffff_fff0);
        Registers { registers }
    }

    /// Get [`Value`] in given [`Register`].
    pub fn get(&mut self, register: Register) -> Value {
        self.registers[register as usize]
    }

    /// Set [`Register`] to given [`Value`] (ignore write to `x0`).
    pub fn set(&mut self, register: Register, value: Value) {
        // ignore writes to x0 (must always be 0)
        if !matches!(register, Register::x0) {
            self.registers[register as usize] = value;
        }
    }
}

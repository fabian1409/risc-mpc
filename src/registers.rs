use crate::{
    error::Error,
    types::{Integer, Value},
};
use serde::{Deserialize, Serialize};
use std::{fmt::Display, str::FromStr};

/// Number of integer registers
const NUM_INTEGER_REGISTERS: usize = 32;
/// Number of float registers
const NUM_FLOAT_REGISTERS: usize = 32;
/// Number of registers
const NUM_REGISTERS: usize = NUM_INTEGER_REGISTERS + NUM_FLOAT_REGISTERS;

/// [`Register`] type to represent the 32 integer and 32 float registers of RISC-V.
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
    f0,
    f1,
    f2,
    f3,
    f4,
    f5,
    f6,
    f7,
    f8,
    f9,
    f10,
    f11,
    f12,
    f13,
    f14,
    f15,
    f16,
    f17,
    f18,
    f19,
    f20,
    f21,
    f22,
    f23,
    f24,
    f25,
    f26,
    f27,
    f28,
    f29,
    f30,
    f31,
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
            "f0" | "ft0" => Ok(Self::f0),
            "f1" | "ft1" => Ok(Self::f1),
            "f2" | "ft2" => Ok(Self::f2),
            "f3" | "ft3" => Ok(Self::f3),
            "f4" | "ft4" => Ok(Self::f4),
            "f5" | "ft5" => Ok(Self::f5),
            "f6" | "ft6" => Ok(Self::f6),
            "f7" | "ft7" => Ok(Self::f7),
            "f8" | "fs0" => Ok(Self::f8),
            "f9" | "fs1" => Ok(Self::f9),
            "f10" | "fa0" => Ok(Self::f10),
            "f11" | "fa1" => Ok(Self::f11),
            "f12" | "fa2" => Ok(Self::f12),
            "f13" | "fa3" => Ok(Self::f13),
            "f14" | "fa4" => Ok(Self::f14),
            "f15" | "fa5" => Ok(Self::f15),
            "f16" | "fa6" => Ok(Self::f16),
            "f17" | "fa7" => Ok(Self::f17),
            "f18" | "fs2" => Ok(Self::f18),
            "f19" | "fs3" => Ok(Self::f19),
            "f20" | "fs4" => Ok(Self::f20),
            "f21" | "fs5" => Ok(Self::f21),
            "f22" | "fs6" => Ok(Self::f22),
            "f23" | "fs7" => Ok(Self::f23),
            "f24" | "fs8" => Ok(Self::f24),
            "f25" | "fs9" => Ok(Self::f25),
            "f26" | "fs10" => Ok(Self::f26),
            "f27" | "fs11" => Ok(Self::f27),
            "f28" | "ft8" => Ok(Self::f28),
            "f29" | "ft9" => Ok(Self::f29),
            "f30" | "ft10" => Ok(Self::f30),
            "f31" | "ft11" => Ok(Self::f31),

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
            Register::f0 => "ft0",
            Register::f1 => "ft1",
            Register::f2 => "ft2",
            Register::f3 => "ft3",
            Register::f4 => "ft4",
            Register::f5 => "ft5",
            Register::f6 => "ft6",
            Register::f7 => "ft7",
            Register::f8 => "fs0",
            Register::f9 => "fs1",
            Register::f10 => "fa0",
            Register::f11 => "fa1",
            Register::f12 => "fa2",
            Register::f13 => "fa3",
            Register::f14 => "fa4",
            Register::f15 => "fa5",
            Register::f16 => "fa6",
            Register::f17 => "fa7",
            Register::f18 => "fs2",
            Register::f19 => "fs3",
            Register::f20 => "fs4",
            Register::f21 => "fs5",
            Register::f22 => "fs6",
            Register::f23 => "fs7",
            Register::f24 => "fs8",
            Register::f25 => "fs9",
            Register::f26 => "fs10",
            Register::f27 => "fs11",
            Register::f28 => "ft8",
            Register::f29 => "ft9",
            Register::f30 => "ft10",
            Register::f31 => "ft11",
        };
        write!(f, "{name}")
    }
}

/// [`Registers`] holds all register values.
#[derive(Debug)]
pub struct Registers {
    registers: [Value; NUM_REGISTERS],
}

impl Registers {
    /// Create all registers with `x0` and `x2(sp)` initialized.
    pub fn new() -> Registers {
        let mut registers = [Value::default(); NUM_REGISTERS];
        // init stack pointer to 8-byte aligned address
        registers[Register::x2 as usize] = Integer::Public(0xffff_ffff_ffff_fff0).into();
        Registers { registers }
    }

    /// Get [`Value`] in given [`Register`].
    pub fn get(&self, register: Register) -> Value {
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

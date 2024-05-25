use crate::{
    error::{Error, Result},
    types::{Integer, Value},
    Float,
};
use serde::{Deserialize, Serialize};
use std::{fmt::Display, str::FromStr};

/// Number of registers
const NUM_REGISTERS: usize = 32;

/// Default vector register len
const DEFAULT_VL: u64 = 64;

/// [`Register`] type to represent registers that are used as inputs.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Register {
    Integer(XRegister),
    Float(FRegister),
}

impl From<XRegister> for Register {
    fn from(val: XRegister) -> Self {
        Register::Integer(val)
    }
}

impl From<FRegister> for Register {
    fn from(val: FRegister) -> Self {
        Register::Float(val)
    }
}

impl TryInto<XRegister> for Register {
    type Error = Error;

    fn try_into(self) -> Result<XRegister> {
        match self {
            Self::Integer(x) => Ok(x),
            Self::Float(_) => Err(Error::UnexpectedRegister),
        }
    }
}

impl TryInto<FRegister> for Register {
    type Error = Error;

    fn try_into(self) -> Result<FRegister> {
        match self {
            Self::Integer(_) => Err(Error::UnexpectedRegister),
            Self::Float(f) => Ok(f),
        }
    }
}

/// [`XRegister`] type to represent the 32 integer registers of RISC-V.
#[allow(non_camel_case_types)]
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum XRegister {
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

impl FromStr for XRegister {
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

impl Display for XRegister {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let name = match self {
            XRegister::x0 => "zero",
            XRegister::x1 => "ra",
            XRegister::x2 => "sp",
            XRegister::x3 => "gp",
            XRegister::x4 => "tp",
            XRegister::x5 => "t0",
            XRegister::x6 => "t1",
            XRegister::x7 => "t2",
            XRegister::x8 => "s0",
            XRegister::x9 => "s1",
            XRegister::x10 => "a0",
            XRegister::x11 => "a1",
            XRegister::x12 => "a2",
            XRegister::x13 => "a3",
            XRegister::x14 => "a4",
            XRegister::x15 => "a5",
            XRegister::x16 => "a6",
            XRegister::x17 => "a7",
            XRegister::x18 => "s2",
            XRegister::x19 => "s3",
            XRegister::x20 => "s4",
            XRegister::x21 => "s5",
            XRegister::x22 => "s6",
            XRegister::x23 => "s7",
            XRegister::x24 => "s8",
            XRegister::x25 => "s9",
            XRegister::x26 => "s10",
            XRegister::x27 => "s11",
            XRegister::x28 => "t3",
            XRegister::x29 => "t4",
            XRegister::x30 => "t5",
            XRegister::x31 => "t6",
        };
        write!(f, "{name}")
    }
}

/// [`FRegister`] type to represent the 32 float registers of RISC-V.
#[allow(non_camel_case_types)]
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum FRegister {
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

impl FromStr for FRegister {
    type Err = Error;

    fn from_str(s: &str) -> std::result::Result<Self, Self::Err> {
        match s {
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

impl Display for FRegister {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let name = match self {
            FRegister::f0 => "ft0",
            FRegister::f1 => "ft1",
            FRegister::f2 => "ft2",
            FRegister::f3 => "ft3",
            FRegister::f4 => "ft4",
            FRegister::f5 => "ft5",
            FRegister::f6 => "ft6",
            FRegister::f7 => "ft7",
            FRegister::f8 => "fs0",
            FRegister::f9 => "fs1",
            FRegister::f10 => "fa0",
            FRegister::f11 => "fa1",
            FRegister::f12 => "fa2",
            FRegister::f13 => "fa3",
            FRegister::f14 => "fa4",
            FRegister::f15 => "fa5",
            FRegister::f16 => "fa6",
            FRegister::f17 => "fa7",
            FRegister::f18 => "fs2",
            FRegister::f19 => "fs3",
            FRegister::f20 => "fs4",
            FRegister::f21 => "fs5",
            FRegister::f22 => "fs6",
            FRegister::f23 => "fs7",
            FRegister::f24 => "fs8",
            FRegister::f25 => "fs9",
            FRegister::f26 => "fs10",
            FRegister::f27 => "fs11",
            FRegister::f28 => "ft8",
            FRegister::f29 => "ft9",
            FRegister::f30 => "ft10",
            FRegister::f31 => "ft11",
        };
        write!(f, "{name}")
    }
}

/// [`VRegister`] type to represent the 32 vector registers of RISC-V.
#[allow(non_camel_case_types)]
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum VRegister {
    v0,
    v1,
    v2,
    v3,
    v4,
    v5,
    v6,
    v7,
    v8,
    v9,
    v10,
    v11,
    v12,
    v13,
    v14,
    v15,
    v16,
    v17,
    v18,
    v19,
    v20,
    v21,
    v22,
    v23,
    v24,
    v25,
    v26,
    v27,
    v28,
    v29,
    v30,
    v31,
}

impl FromStr for VRegister {
    type Err = Error;

    fn from_str(s: &str) -> std::result::Result<Self, Self::Err> {
        match s {
            "v0" => Ok(Self::v0),
            "v1" => Ok(Self::v1),
            "v2" => Ok(Self::v2),
            "v3" => Ok(Self::v3),
            "v4" => Ok(Self::v4),
            "v5" => Ok(Self::v5),
            "v6" => Ok(Self::v6),
            "v7" => Ok(Self::v7),
            "v8" => Ok(Self::v8),
            "v9" => Ok(Self::v9),
            "v10" => Ok(Self::v10),
            "v11" => Ok(Self::v11),
            "v12" => Ok(Self::v12),
            "v13" => Ok(Self::v13),
            "v14" => Ok(Self::v14),
            "v15" => Ok(Self::v15),
            "v16" => Ok(Self::v16),
            "v17" => Ok(Self::v17),
            "v18" => Ok(Self::v18),
            "v19" => Ok(Self::v19),
            "v20" => Ok(Self::v20),
            "v21" => Ok(Self::v21),
            "v22" => Ok(Self::v22),
            "v23" => Ok(Self::v23),
            "v24" => Ok(Self::v24),
            "v25" => Ok(Self::v25),
            "v26" => Ok(Self::v26),
            "v27" => Ok(Self::v27),
            "v28" => Ok(Self::v28),
            "v29" => Ok(Self::v29),
            "v30" => Ok(Self::v30),
            "v31" => Ok(Self::v31),
            _ => Err(Error::ParseRegisterError(s.to_owned())),
        }
    }
}

impl Display for VRegister {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let name = match self {
            VRegister::v0 => "v0",
            VRegister::v1 => "v1",
            VRegister::v2 => "v2",
            VRegister::v3 => "v3",
            VRegister::v4 => "v4",
            VRegister::v5 => "v5",
            VRegister::v6 => "v6",
            VRegister::v7 => "v7",
            VRegister::v8 => "v8",
            VRegister::v9 => "v9",
            VRegister::v10 => "v10",
            VRegister::v11 => "v11",
            VRegister::v12 => "v12",
            VRegister::v13 => "v13",
            VRegister::v14 => "v14",
            VRegister::v15 => "v15",
            VRegister::v16 => "v16",
            VRegister::v17 => "v17",
            VRegister::v18 => "v18",
            VRegister::v19 => "v19",
            VRegister::v20 => "v20",
            VRegister::v21 => "v21",
            VRegister::v22 => "v22",
            VRegister::v23 => "v23",
            VRegister::v24 => "v24",
            VRegister::v25 => "v25",
            VRegister::v26 => "v26",
            VRegister::v27 => "v27",
            VRegister::v28 => "v28",
            VRegister::v29 => "v29",
            VRegister::v30 => "v30",
            VRegister::v31 => "v31",
        };
        write!(f, "{name}")
    }
}

/// [`XRegisters`] holds all integer registers.
#[derive(Debug)]
pub struct XRegisters {
    registers: [Integer; NUM_REGISTERS],
}

impl XRegisters {
    /// Create all registers with `x0` and `x2(sp)` initialized.
    pub fn new() -> XRegisters {
        let mut registers = [Integer::default(); NUM_REGISTERS];
        // init stack pointer to 8-byte aligned address
        registers[XRegister::x2 as usize] = Integer::Public(0xffff_ffff_ffff_fff0);
        XRegisters { registers }
    }

    /// Get [`Integer`] in given [`XRegister`].
    pub fn get(&self, register: XRegister) -> Integer {
        self.registers[register as usize]
    }

    /// Set [`XRegister`] to given [`Integer`] (ignore write to `x0`).
    pub fn set(&mut self, register: XRegister, value: Integer) {
        // ignore writes to x0 (must always be 0)
        if !matches!(register, XRegister::x0) {
            self.registers[register as usize] = value;
        }
    }
}

/// [`FRegisters`] holds all float registers.
#[derive(Debug)]
pub struct FRegisters {
    registers: [Float; NUM_REGISTERS],
}

impl FRegisters {
    pub fn new() -> FRegisters {
        FRegisters {
            registers: Default::default(),
        }
    }

    /// Get [`Float`] in given [`FRegister`].
    pub fn get(&self, register: FRegister) -> Float {
        self.registers[register as usize]
    }

    /// Set [`FRegister`] to given [`Float`].
    pub fn set(&mut self, register: FRegister, value: Float) {
        self.registers[register as usize] = value;
    }
}

/// [`VRegisters`] holds all vector registers.
#[derive(Debug)]
pub struct VRegisters {
    pub vl: u64,
    registers: [Vec<Value>; NUM_REGISTERS],
}

impl VRegisters {
    pub fn new() -> VRegisters {
        VRegisters {
            vl: DEFAULT_VL,
            registers: Default::default(),
        }
    }

    /// Get [`Vec<Value>`] in given [`VRegister`].
    pub fn get(&self, register: VRegister) -> &[Value] {
        &self.registers[register as usize]
    }

    /// Set [`VRegister`] to given [`Vec<Value>`].
    pub fn set(&mut self, register: VRegister, v: Vec<Value>) {
        self.registers[register as usize] = v;
    }
}

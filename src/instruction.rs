use crate::{
    error::Error,
    registers::{FRegister, VRegister, XRegister},
};
use std::{fmt::Display, str::FromStr};

/// [`Label`] represents either a [`Text`] or [`Numeric`] label.
///
/// [`Text`]: Label::Text
/// [`Numeric`]: Label::Numeric
#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub enum Label {
    Text(String),
    Numeric(String),
}

impl FromStr for Label {
    type Err = Error;

    fn from_str(s: &str) -> std::result::Result<Self, Self::Err> {
        if s.chars().all(|c| c.is_ascii_digit())
            | ((s.ends_with('f') | s.ends_with('b'))
                & s.chars().rev().skip(1).all(|c| c.is_ascii_digit()))
        {
            Ok(Self::Numeric(s.to_string()))
        } else {
            Ok(Self::Text(s.to_string()))
        }
    }
}

impl Display for Label {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Text(label) => write!(f, "{label}"),
            Self::Numeric(label) => write!(f, "{label}"),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VType {
    E64,
}

/// [`Instruction`] represents all supported RISC-V instructions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Instruction {
    ADD {
        rd: XRegister,
        rs1: XRegister,
        rs2: XRegister,
    },
    ADDI {
        rd: XRegister,
        rs1: XRegister,
        imm: i32,
    },
    AND {
        rd: XRegister,
        rs1: XRegister,
        rs2: XRegister,
    },
    ANDI {
        rd: XRegister,
        rs1: XRegister,
        imm: i32,
    },
    AUIPC {
        rd: XRegister,
        imm: i32,
    },
    BEQ {
        rs1: XRegister,
        rs2: XRegister,
        label: Label,
    },
    BGE {
        rs1: XRegister,
        rs2: XRegister,
        label: Label,
    },
    BLT {
        rs1: XRegister,
        rs2: XRegister,
        label: Label,
    },
    BNE {
        rs1: XRegister,
        rs2: XRegister,
        label: Label,
    },
    DIV {
        rd: XRegister,
        rs1: XRegister,
        rs2: XRegister,
    },
    REM {
        rd: XRegister,
        rs1: XRegister,
        rs2: XRegister,
    },
    JAL {
        rd: XRegister,
        label: Label,
    },
    JALR {
        rd: XRegister,
        rs1: XRegister,
        offset: i32,
    },
    LD {
        rd: XRegister,
        offset: i32,
        rs1: XRegister,
    },
    LUI {
        rd: XRegister,
        imm: i32,
    },
    MUL {
        rd: XRegister,
        rs1: XRegister,
        rs2: XRegister,
    },
    OR {
        rd: XRegister,
        rs1: XRegister,
        rs2: XRegister,
    },
    ORI {
        rd: XRegister,
        rs1: XRegister,
        imm: i32,
    },
    SD {
        rs2: XRegister,
        offset: i32,
        rs1: XRegister,
    },
    SLL {
        rd: XRegister,
        rs1: XRegister,
        rs2: XRegister,
    },
    SLLI {
        rd: XRegister,
        rs1: XRegister,
        shamt: u8,
    },
    SLT {
        rd: XRegister,
        rs1: XRegister,
        rs2: XRegister,
    },
    SLTI {
        rd: XRegister,
        rs1: XRegister,
        imm: i32,
    },
    SRL {
        rd: XRegister,
        rs1: XRegister,
        rs2: XRegister,
    },
    SRLI {
        rd: XRegister,
        rs1: XRegister,
        shamt: u8,
    },
    SUB {
        rd: XRegister,
        rs1: XRegister,
        rs2: XRegister,
    },
    XOR {
        rd: XRegister,
        rs1: XRegister,
        rs2: XRegister,
    },
    XORI {
        rd: XRegister,
        rs1: XRegister,
        imm: i32,
    },
    NOP,
    LI {
        rd: XRegister,
        imm: i32,
    },
    MV {
        rd: XRegister,
        rs1: XRegister,
    },
    NOT {
        rd: XRegister,
        rs1: XRegister,
    },
    NEG {
        rd: XRegister,
        rs1: XRegister,
    },
    SEQZ {
        rd: XRegister,
        rs1: XRegister,
    },
    SNEZ {
        rd: XRegister,
        rs1: XRegister,
    },
    SLTZ {
        rd: XRegister,
        rs1: XRegister,
    },
    SGTZ {
        rd: XRegister,
        rs1: XRegister,
    },
    BEQZ {
        rs1: XRegister,
        label: Label,
    },
    BNEZ {
        rs1: XRegister,
        label: Label,
    },
    BLEZ {
        rs1: XRegister,
        label: Label,
    },
    BGEZ {
        rs1: XRegister,
        label: Label,
    },
    BLTZ {
        rs1: XRegister,
        label: Label,
    },
    BGTZ {
        rs1: XRegister,
        label: Label,
    },
    BGT {
        rs1: XRegister,
        rs2: XRegister,
        label: Label,
    },
    BLE {
        rs1: XRegister,
        rs2: XRegister,
        label: Label,
    },
    J {
        label: Label,
    },
    JR {
        rs1: XRegister,
    },
    RET,
    CALL {
        label: Label,
    },
    TAIL {
        label: Label,
    },
    Label(Label),
    FADD {
        rd: FRegister,
        rs1: FRegister,
        rs2: FRegister,
    },
    FSUB {
        rd: FRegister,
        rs1: FRegister,
        rs2: FRegister,
    },
    FMUL {
        rd: FRegister,
        rs1: FRegister,
        rs2: FRegister,
    },
    FDIV {
        rd: FRegister,
        rs1: FRegister,
        rs2: FRegister,
    },
    FMIN {
        rd: FRegister,
        rs1: FRegister,
        rs2: FRegister,
    },
    FMAX {
        rd: FRegister,
        rs1: FRegister,
        rs2: FRegister,
    },
    FSQRT {
        rd: FRegister,
        rs1: FRegister,
    },
    FLD {
        rd: FRegister,
        offset: i32,
        rs1: XRegister,
    },
    FSD {
        rs2: FRegister,
        offset: i32,
        rs1: XRegister,
    },
    FMADD {
        rd: FRegister,
        rs1: FRegister,
        rs2: FRegister,
        rs3: FRegister,
    },
    FMSUB {
        rd: FRegister,
        rs1: FRegister,
        rs2: FRegister,
        rs3: FRegister,
    },
    FNMADD {
        rd: FRegister,
        rs1: FRegister,
        rs2: FRegister,
        rs3: FRegister,
    },
    FNMSUB {
        rd: FRegister,
        rs1: FRegister,
        rs2: FRegister,
        rs3: FRegister,
    },
    FCVTLUD {
        rd: XRegister,
        rs1: FRegister,
    },
    FCVTDLU {
        rd: FRegister,
        rs1: XRegister,
    },
    FMV {
        rd: FRegister,
        rs1: FRegister,
    },
    FMVXD {
        rd: XRegister,
        rs1: FRegister,
    },
    FMVDX {
        rd: FRegister,
        rs1: XRegister,
    },
    FSGNJ {
        rd: FRegister,
        rs1: FRegister,
        rs2: FRegister,
    },
    FSGNJN {
        rd: FRegister,
        rs1: FRegister,
        rs2: FRegister,
    },
    FSGNJX {
        rd: FRegister,
        rs1: FRegister,
        rs2: FRegister,
    },
    FEQ {
        rd: XRegister,
        rs1: FRegister,
        rs2: FRegister,
    },
    FLT {
        rd: XRegister,
        rs1: FRegister,
        rs2: FRegister,
    },
    FLE {
        rd: XRegister,
        rs1: FRegister,
        rs2: FRegister,
    },
    FCLASS {
        rd: XRegister,
        rs1: FRegister,
    },
    FNEG {
        rd: FRegister,
        rs1: FRegister,
    },
    FABS {
        rd: FRegister,
        rs1: FRegister,
    },
    VSETVL {
        rd: XRegister,
        rs1: XRegister,
        rs2: XRegister,
    },
    VSETVLI {
        rd: XRegister,
        rs1: XRegister,
        imm: VType,
    },
    VLE {
        vd: VRegister,
        rs1: XRegister,
        // vm: VRegister,
    },
    VSE {
        vs2: VRegister,
        rs1: XRegister,
        // vm: VRegister,
    },
    VMULVV {
        vd: VRegister,
        vs1: VRegister,
        vs2: VRegister,
        // vm: VRegister,
    },
    VMULVX {
        vd: VRegister,
        rs1: XRegister,
        vs2: VRegister,
        // vm: VRegister,
    },
    VFMULVV {
        vd: VRegister,
        vs1: VRegister,
        vs2: VRegister,
        // vm: VRegister,
    },
    VFMULVF {
        vd: VRegister,
        rs1: FRegister,
        vs2: VRegister,
        // vm: VRegister,
    },
    VANDVV {
        vd: VRegister,
        vs1: VRegister,
        vs2: VRegister,
        // vm: VRegister,
    },
    VANDVX {
        vd: VRegister,
        rs1: XRegister,
        vs2: VRegister,
        // vm: VRegister,
    },
    VANDVI {
        vd: VRegister,
        imm: i32,
        vs2: VRegister,
        // vm: VRegister,
    },
}

fn parse_offset_rs1(s: &str) -> std::result::Result<(&str, &str), Error> {
    match s.split('(').collect::<Vec<_>>()[..] {
        [offset, rs1] => Ok((offset, rs1.strip_suffix(')').unwrap())),
        _ => Err(Error::ParseOffsetError(s.to_owned())),
    }
}

impl FromStr for Instruction {
    type Err = Error;

    fn from_str(s: &str) -> std::result::Result<Self, Self::Err> {
        let (instruction, operands) = s.trim().split_once(' ').unwrap_or((s.trim(), ""));
        let ops: Vec<&str> = operands.trim().split(',').map(str::trim).collect();
        match (instruction, ops.as_slice()) {
            ("add", [rd, rs1, rs2]) => Ok(Self::ADD {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
                rs2: rs2.parse()?,
            }),
            ("sub", [rd, rs1, rs2]) => Ok(Self::SUB {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
                rs2: rs2.parse()?,
            }),
            ("mul", [rd, rs1, rs2]) => Ok(Self::MUL {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
                rs2: rs2.parse()?,
            }),
            ("div" | "divu", [rd, rs1, rs2]) => Ok(Self::DIV {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
                rs2: rs2.parse()?,
            }),
            ("rem" | "remu", [rd, rs1, rs2]) => Ok(Self::REM {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
                rs2: rs2.parse()?,
            }),
            ("and", [rd, rs1, rs2]) => Ok(Self::AND {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
                rs2: rs2.parse()?,
            }),
            ("xor", [rd, rs1, rs2]) => Ok(Self::XOR {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
                rs2: rs2.parse()?,
            }),
            ("or", [rd, rs1, rs2]) => Ok(Self::OR {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
                rs2: rs2.parse()?,
            }),
            ("sll", [rd, rs1, rs2]) => Ok(Self::SLL {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
                rs2: rs2.parse()?,
            }),
            ("slli", [rd, rs1, shamt]) => Ok(Self::SLLI {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
                shamt: shamt.parse()?,
            }),
            ("srl", [rd, rs1, rs2]) => Ok(Self::SRL {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
                rs2: rs2.parse()?,
            }),
            ("srli", [rd, rs1, shamt]) => Ok(Self::SRLI {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
                shamt: shamt.parse()?,
            }),
            ("beq", [rs1, rs2, label]) => Ok(Self::BEQ {
                rs1: rs1.parse()?,
                rs2: rs2.parse()?,
                label: label.parse()?,
            }),
            ("bne", [rs1, rs2, label]) => Ok(Self::BNE {
                rs1: rs1.parse()?,
                rs2: rs2.parse()?,
                label: label.parse()?,
            }),
            ("blt" | "bltu", [rs1, rs2, label]) => Ok(Self::BLT {
                rs1: rs1.parse()?,
                rs2: rs2.parse()?,
                label: label.parse()?,
            }),
            ("bge" | "bgeu", [rs1, rs2, label]) => Ok(Self::BGE {
                rs1: rs1.parse()?,
                rs2: rs2.parse()?,
                label: label.parse()?,
            }),
            ("jal", [rd, label]) => Ok(Self::JAL {
                rd: rd.parse()?,
                label: label.parse()?,
            }),
            ("jalr", [rd, rs1, offset]) => Ok(Self::JALR {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
                offset: offset.parse()?,
            }),
            ("addi", [rd, rs1, imm]) => Ok(Self::ADDI {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
                imm: imm.parse()?,
            }),
            ("xori", [rd, rs1, imm]) => Ok(Self::XORI {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
                imm: imm.parse()?,
            }),
            ("andi", [rd, rs1, imm]) => Ok(Self::ANDI {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
                imm: imm.parse()?,
            }),
            ("ori", [rd, rs1, imm]) => Ok(Self::ORI {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
                imm: imm.parse()?,
            }),
            ("ld", [rd, offset_rs1]) => {
                let (offset, rs1) = parse_offset_rs1(offset_rs1)?;
                Ok(Self::LD {
                    rd: rd.parse()?,
                    offset: offset.parse()?,
                    rs1: rs1.parse()?,
                })
            }
            ("sd", [rs2, offset_rs1]) => {
                let (offset, rs1) = parse_offset_rs1(offset_rs1)?;
                Ok(Self::SD {
                    rs2: rs2.parse()?,
                    offset: offset.parse()?,
                    rs1: rs1.parse()?,
                })
            }
            ("slti", [rd, rs1, imm]) => Ok(Self::SLTI {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
                imm: imm.parse()?,
            }),
            ("lui", [rd, imm]) => Ok(Self::LUI {
                rd: rd.parse()?,
                imm: imm.parse()?,
            }),
            ("auipc", [rd, imm]) => Ok(Self::AUIPC {
                rd: rd.parse()?,
                imm: imm.parse()?,
            }),
            ("nop", [""]) => Ok(Self::NOP),
            ("li", [rd, imm]) => Ok(Self::LI {
                rd: rd.parse()?,
                imm: imm.parse()?,
            }),
            ("mv", [rd, rs1]) => Ok(Self::MV {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
            }),
            ("not", [rd, rs1]) => Ok(Self::NOT {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
            }),
            ("neg", [rd, rs1]) => Ok(Self::NEG {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
            }),
            ("slt" | "sltu", [rd, rs1, rs2]) => Ok(Self::SLT {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
                rs2: rs2.parse()?,
            }),
            ("seqz", [rd, rs1]) => Ok(Self::SEQZ {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
            }),
            ("snez", [rd, rs1]) => Ok(Self::SNEZ {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
            }),
            ("sltz", [rd, rs1]) => Ok(Self::SLTZ {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
            }),
            ("sgtz", [rd, rs1]) => Ok(Self::SGTZ {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
            }),
            ("beqz", [rs1, label]) => Ok(Self::BEQZ {
                rs1: rs1.parse()?,
                label: label.parse()?,
            }),
            ("bnez", [rs1, label]) => Ok(Self::BNEZ {
                rs1: rs1.parse()?,
                label: label.parse()?,
            }),
            ("blez", [rs1, label]) => Ok(Self::BLEZ {
                rs1: rs1.parse()?,
                label: label.parse()?,
            }),
            ("bgez", [rs1, label]) => Ok(Self::BGEZ {
                rs1: rs1.parse()?,
                label: label.parse()?,
            }),
            ("bltz", [rs1, label]) => Ok(Self::BLTZ {
                rs1: rs1.parse()?,
                label: label.parse()?,
            }),
            ("bgtz", [rs1, label]) => Ok(Self::BGTZ {
                rs1: rs1.parse()?,
                label: label.parse()?,
            }),
            ("bgt", [rs1, rs2, label]) => Ok(Self::BGT {
                rs1: rs1.parse()?,
                rs2: rs2.parse()?,
                label: label.parse()?,
            }),
            ("ble", [rs1, rs2, label]) => Ok(Self::BLE {
                rs1: rs1.parse()?,
                rs2: rs2.parse()?,
                label: label.parse()?,
            }),
            ("j", [label]) => Ok(Self::J {
                label: label.parse()?,
            }),
            ("jr", [rs1]) => Ok(Self::JR { rs1: rs1.parse()? }),
            ("call", [label]) => Ok(Self::CALL {
                label: label.parse()?,
            }),
            ("tail", [label]) => Ok(Self::TAIL {
                label: label.parse()?,
            }),
            ("ret", [""]) => Ok(Self::RET),
            ("fadd.d", [rd, rs1, rs2]) => Ok(Self::FADD {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
                rs2: rs2.parse()?,
            }),
            ("fsub.d", [rd, rs1, rs2]) => Ok(Self::FSUB {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
                rs2: rs2.parse()?,
            }),
            ("fmul.d", [rd, rs1, rs2]) => Ok(Self::FMUL {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
                rs2: rs2.parse()?,
            }),
            ("fdiv.d", [rd, rs1, rs2]) => Ok(Self::FDIV {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
                rs2: rs2.parse()?,
            }),
            ("fmin.d", [rd, rs1, rs2]) => Ok(Self::FMIN {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
                rs2: rs2.parse()?,
            }),
            ("fmax.d", [rd, rs1, rs2]) => Ok(Self::FMAX {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
                rs2: rs2.parse()?,
            }),
            ("fsqrt.d", [rd, rs1]) => Ok(Self::FSQRT {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
            }),
            ("fld", [rd, offset_rs1]) => {
                let (offset, rs1) = parse_offset_rs1(offset_rs1)?;
                Ok(Self::FLD {
                    rd: rd.parse()?,
                    offset: offset.parse()?,
                    rs1: rs1.parse()?,
                })
            }
            ("fsd", [rs2, offset_rs1]) => {
                let (offset, rs1) = parse_offset_rs1(offset_rs1)?;
                Ok(Self::FSD {
                    rs2: rs2.parse()?,
                    offset: offset.parse()?,
                    rs1: rs1.parse()?,
                })
            }
            ("fmadd.d", [rd, rs1, rs2, rs3]) => Ok(Self::FMADD {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
                rs2: rs2.parse()?,
                rs3: rs3.parse()?,
            }),
            ("fmsub.d", [rd, rs1, rs2, rs3]) => Ok(Self::FMSUB {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
                rs2: rs2.parse()?,
                rs3: rs3.parse()?,
            }),
            ("fnmadd.d", [rd, rs1, rs2, rs3]) => Ok(Self::FNMADD {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
                rs2: rs2.parse()?,
                rs3: rs3.parse()?,
            }),
            ("fnmsub.d", [rd, rs1, rs2, rs3]) => Ok(Self::FNMSUB {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
                rs2: rs2.parse()?,
                rs3: rs3.parse()?,
            }),
            ("fcvt.lu.d", [rd, rs1]) => Ok(Self::FCVTLUD {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
            }),
            ("fcvt.d.lu", [rd, rs1]) => Ok(Self::FCVTDLU {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
            }),
            ("fmv.d", [rd, rs1]) => Ok(Self::FMV {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
            }),
            ("fmv.x.d", [rd, rs1]) => Ok(Self::FMVXD {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
            }),
            ("fmv.d.x", [rd, rs1]) => Ok(Self::FMVDX {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
            }),
            ("fsgnj.d", [rd, rs1, rs2]) => Ok(Self::FSGNJ {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
                rs2: rs2.parse()?,
            }),
            ("fsgnjn.d", [rd, rs1, rs2]) => Ok(Self::FSGNJN {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
                rs2: rs2.parse()?,
            }),
            ("fsgnjx.d", [rd, rs1, rs2]) => Ok(Self::FSGNJX {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
                rs2: rs2.parse()?,
            }),
            ("feq.d", [rd, rs1, rs2]) => Ok(Self::FEQ {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
                rs2: rs2.parse()?,
            }),
            ("flt.d", [rd, rs1, rs2]) => Ok(Self::FLT {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
                rs2: rs2.parse()?,
            }),
            ("fle.d", [rd, rs1, rs2]) => Ok(Self::FLE {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
                rs2: rs2.parse()?,
            }),
            ("fclass.d", [rd, rs1]) => Ok(Self::FCLASS {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
            }),
            ("fneg.d", [rd, rs1]) => Ok(Self::FNEG {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
            }),
            ("fabs.d", [rd, rs1]) => Ok(Self::FABS {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
            }),
            ("vsetvl", [rd, rs1, rs2]) => Ok(Self::VSETVL {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
                rs2: rs2.parse()?,
            }),
            ("vsetvli", [rd, rs1, "e64"]) => Ok(Self::VSETVLI {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
                imm: VType::E64,
            }),
            ("vle.v", [vd, rs1]) => Ok(Self::VLE {
                vd: vd.parse()?,
                rs1: rs1.parse()?,
            }),
            ("vse.v", [vs2, rs1]) => Ok(Self::VSE {
                vs2: vs2.parse()?,
                rs1: rs1.parse()?,
            }),
            ("vmul.vv", [vd, vs1, vs2]) => Ok(Self::VMULVV {
                vd: vd.parse()?,
                vs1: vs1.parse()?,
                vs2: vs2.parse()?,
            }),
            ("vmul.vx", [vd, rs1, vs2]) => Ok(Self::VMULVX {
                vd: vd.parse()?,
                rs1: rs1.parse()?,
                vs2: vs2.parse()?,
            }),
            ("vfmul.vv", [vd, vs1, vs2]) => Ok(Self::VFMULVV {
                vd: vd.parse()?,
                vs1: vs1.parse()?,
                vs2: vs2.parse()?,
            }),
            ("vfmul.vf", [vd, rs1, vs2]) => Ok(Self::VFMULVF {
                vd: vd.parse()?,
                rs1: rs1.parse()?,
                vs2: vs2.parse()?,
            }),
            ("vand.vv", [vd, vs1, vs2]) => Ok(Self::VANDVV {
                vd: vd.parse()?,
                vs1: vs1.parse()?,
                vs2: vs2.parse()?,
            }),
            ("vand.vx", [vd, rs1, vs2]) => Ok(Self::VANDVX {
                vd: vd.parse()?,
                rs1: rs1.parse()?,
                vs2: vs2.parse()?,
            }),
            ("vand.vi", [vd, imm, vs2]) => Ok(Self::VANDVI {
                vd: vd.parse()?,
                imm: imm.parse()?,
                vs2: vs2.parse()?,
            }),
            _ => {
                if s.ends_with(':') {
                    Ok(Self::Label(s.strip_suffix(':').unwrap().parse()?))
                } else {
                    Err(Error::ParseInstructionError(s.to_string()))
                }
            }
        }
    }
}

impl Display for Instruction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Instruction::ADD { rd, rs1, rs2 } => write!(f, "add {rd},{rs1},{rs2}"),
            Instruction::ADDI { rd, rs1, imm } => write!(f, "addi {rd},{rs1},{imm}"),
            Instruction::AND { rd, rs1, rs2 } => write!(f, "and {rd},{rs1},{rs2}"),
            Instruction::ANDI { rd, rs1, imm } => write!(f, "andi {rd},{rs1},{imm}"),
            Instruction::AUIPC { rd, imm } => write!(f, "auipc {rd},{imm}"),
            Instruction::BEQ { rs1, rs2, label } => write!(f, "beq {rs1},{rs2},{label}"),
            Instruction::BGE { rs1, rs2, label } => write!(f, "bge {rs1},{rs2},{label}"),
            Instruction::BLT { rs1, rs2, label } => write!(f, "blt {rs1},{rs2},{label}"),
            Instruction::BNE { rs1, rs2, label } => write!(f, "bne {rs1},{rs2},{label}"),
            Instruction::JAL { rd, label } => write!(f, "jal {rd},{label}"),
            Instruction::JALR { rd, rs1, offset } => write!(f, "jalr {rd},{rs1},{offset}"),
            Instruction::LD { rd, offset, rs1 } => write!(f, "ld {rd},{offset}({rs1})"),
            Instruction::LUI { rd, imm } => write!(f, "lui {rd},{imm}"),
            Instruction::MUL { rd, rs1, rs2 } => write!(f, "mul {rd},{rs1},{rs2}"),
            Instruction::DIV { rd, rs1, rs2 } => write!(f, "div {rd},{rs1},{rs2}"),
            Instruction::REM { rd, rs1, rs2 } => write!(f, "rem {rd},{rs1},{rs2}"),
            Instruction::OR { rd, rs1, rs2 } => write!(f, "or {rd},{rs1},{rs2}"),
            Instruction::ORI { rd, rs1, imm } => write!(f, "ori {rd},{rs1},{imm}"),
            Instruction::SD { rs2, offset, rs1 } => write!(f, "sd {rs2},{offset}({rs1})"),
            Instruction::SLL { rd, rs1, rs2 } => write!(f, "sll {rd},{rs1},{rs2}"),
            Instruction::SLLI { rd, rs1, shamt } => write!(f, "slli {rd},{rs1},{shamt}"),
            Instruction::SLTI { rd, rs1, imm } => write!(f, "slti {rd},{rs1},{imm}"),
            Instruction::SRL { rd, rs1, rs2 } => write!(f, "srl {rd},{rs1},{rs2}"),
            Instruction::SRLI { rd, rs1, shamt } => write!(f, "srli {rd},{rs1},{shamt}"),
            Instruction::SUB { rd, rs1, rs2 } => write!(f, "sub {rd},{rs1},{rs2}"),
            Instruction::XOR { rd, rs1, rs2 } => write!(f, "xor {rd},{rs1},{rs2}"),
            Instruction::XORI { rd, rs1, imm } => write!(f, "xori {rd},{rs1},{imm}"),
            Instruction::NOP => write!(f, "nop"),
            Instruction::LI { rd, imm } => write!(f, "li {rd},{imm}"),
            Instruction::MV { rd, rs1 } => write!(f, "mv {rd},{rs1}"),
            Instruction::NOT { rd, rs1 } => write!(f, "not {rd},{rs1}"),
            Instruction::NEG { rd, rs1 } => write!(f, "neg {rd},{rs1}"),
            Instruction::SLT { rd, rs1, rs2 } => write!(f, "slt {rd},{rs1},{rs2}"),
            Instruction::SEQZ { rd, rs1 } => write!(f, "seqz {rd},{rs1}"),
            Instruction::SNEZ { rd, rs1 } => write!(f, "snez {rd},{rs1}"),
            Instruction::SLTZ { rd, rs1 } => write!(f, "sltz {rd},{rs1}"),
            Instruction::SGTZ { rd, rs1 } => write!(f, "sgtz {rd},{rs1}"),
            Instruction::BEQZ { rs1, label } => write!(f, "beqz {rs1},{label}"),
            Instruction::BNEZ { rs1, label } => write!(f, "bnez {rs1},{label}"),
            Instruction::BLEZ { rs1, label } => write!(f, "blez {rs1},{label}"),
            Instruction::BGEZ { rs1, label } => write!(f, "bgez {rs1},{label}"),
            Instruction::BLTZ { rs1, label } => write!(f, "bltz {rs1},{label}"),
            Instruction::BGTZ { rs1, label } => write!(f, "bgtz {rs1},{label}"),
            Instruction::BGT { rs1, rs2, label } => write!(f, "bgt {rs1},{rs2},{label}]"),
            Instruction::BLE { rs1, rs2, label } => write!(f, "ble {rs1},{rs2},{label}"),
            Instruction::J { label } => write!(f, "j {label}"),
            Instruction::JR { rs1 } => write!(f, "jr {rs1}"),
            Instruction::RET => write!(f, "ret"),
            Instruction::CALL { label } => write!(f, "call {label}"),
            Instruction::TAIL { label } => write!(f, "tail {label}"),
            Instruction::Label(label) => write!(f, "{label}:"),
            _ => todo!(),
        }
    }
}

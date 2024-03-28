use crate::{
    error::{Error, Result},
    registers::Register,
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

/// [`Instruction`] represents all supported RISC-V instructions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Instruction {
    Add {
        rd: Register,
        rs1: Register,
        rs2: Register,
    },
    Addi {
        rd: Register,
        rs1: Register,
        imm: i32,
    },
    And {
        rd: Register,
        rs1: Register,
        rs2: Register,
    },
    Andi {
        rd: Register,
        rs1: Register,
        imm: i32,
    },
    Auipc {
        rd: Register,
        imm: i32,
    },
    Beq {
        rs1: Register,
        rs2: Register,
        label: Label,
    },
    Bge {
        rs1: Register,
        rs2: Register,
        label: Label,
    },
    Blt {
        rs1: Register,
        rs2: Register,
        label: Label,
    },
    Bne {
        rs1: Register,
        rs2: Register,
        label: Label,
    },
    Div {
        rd: Register,
        rs1: Register,
        rs2: Register,
    },
    Rem {
        rd: Register,
        rs1: Register,
        rs2: Register,
    },
    Jal {
        rd: Register,
        label: Label,
    },
    Jalr {
        rd: Register,
        rs1: Register,
        offset: i32,
    },
    Ld {
        rd: Register,
        offset: i32,
        rs1: Register,
    },
    Lui {
        rd: Register,
        imm: i32,
    },
    Mul {
        rd: Register,
        rs1: Register,
        rs2: Register,
    },
    Or {
        rd: Register,
        rs1: Register,
        rs2: Register,
    },
    Ori {
        rd: Register,
        rs1: Register,
        imm: i32,
    },
    Sd {
        rs2: Register,
        offset: i32,
        rs1: Register,
    },
    Sll {
        rd: Register,
        rs1: Register,
        rs2: Register,
    },
    Slli {
        rd: Register,
        rs1: Register,
        shamt: u8,
    },
    Slt {
        rd: Register,
        rs1: Register,
        rs2: Register,
    },
    Slti {
        rd: Register,
        rs1: Register,
        imm: i32,
    },
    Srl {
        rd: Register,
        rs1: Register,
        rs2: Register,
    },
    Srli {
        rd: Register,
        rs1: Register,
        shamt: u8,
    },
    Sub {
        rd: Register,
        rs1: Register,
        rs2: Register,
    },
    Xor {
        rd: Register,
        rs1: Register,
        rs2: Register,
    },
    Xori {
        rd: Register,
        rs1: Register,
        imm: i32,
    },
    Nop,
    Li {
        rd: Register,
        imm: i32,
    },
    Mv {
        rd: Register,
        rs1: Register,
    },
    Not {
        rd: Register,
        rs1: Register,
    },
    Neg {
        rd: Register,
        rs1: Register,
    },
    Seqz {
        rd: Register,
        rs1: Register,
    },
    Snez {
        rd: Register,
        rs1: Register,
    },
    Sltz {
        rd: Register,
        rs1: Register,
    },
    Sgtz {
        rd: Register,
        rs1: Register,
    },
    Beqz {
        rs1: Register,
        label: Label,
    },
    Bnez {
        rs1: Register,
        label: Label,
    },
    Blez {
        rs1: Register,
        label: Label,
    },
    Bgez {
        rs1: Register,
        label: Label,
    },
    Bltz {
        rs1: Register,
        label: Label,
    },
    Bgtz {
        rs1: Register,
        label: Label,
    },
    Bgt {
        rs1: Register,
        rs2: Register,
        label: Label,
    },
    Ble {
        rs1: Register,
        rs2: Register,
        label: Label,
    },
    J {
        label: Label,
    },
    Jr {
        rs1: Register,
    },
    Ret,
    Call {
        label: Label,
    },
    Label(Label),
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
            ("add", [rd, rs1, rs2]) => Ok(Self::Add {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
                rs2: rs2.parse()?,
            }),
            ("sub", [rd, rs1, rs2]) => Ok(Self::Sub {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
                rs2: rs2.parse()?,
            }),
            ("mul", [rd, rs1, rs2]) => Ok(Self::Mul {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
                rs2: rs2.parse()?,
            }),
            ("div", [rd, rs1, rs2]) => Ok(Self::Div {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
                rs2: rs2.parse()?,
            }),
            ("rem", [rd, rs1, rs2]) => Ok(Self::Rem {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
                rs2: rs2.parse()?,
            }),
            ("and", [rd, rs1, rs2]) => Ok(Self::And {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
                rs2: rs2.parse()?,
            }),
            ("xor", [rd, rs1, rs2]) => Ok(Self::Xor {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
                rs2: rs2.parse()?,
            }),
            ("or", [rd, rs1, rs2]) => Ok(Self::Or {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
                rs2: rs2.parse()?,
            }),
            ("sll", [rd, rs1, rs2]) => Ok(Self::Sll {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
                rs2: rs2.parse()?,
            }),
            ("slli", [rd, rs1, shamt]) => Ok(Self::Slli {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
                shamt: shamt.parse()?,
            }),
            ("srl", [rd, rs1, rs2]) => Ok(Self::Srl {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
                rs2: rs2.parse()?,
            }),
            ("srli", [rd, rs1, shamt]) => Ok(Self::Srli {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
                shamt: shamt.parse()?,
            }),
            ("beq", [rs1, rs2, label]) => Ok(Self::Beq {
                rs1: rs1.parse()?,
                rs2: rs2.parse()?,
                label: label.parse()?,
            }),
            ("bne", [rs1, rs2, label]) => Ok(Self::Bne {
                rs1: rs1.parse()?,
                rs2: rs2.parse()?,
                label: label.parse()?,
            }),
            ("blt" | "bltu", [rs1, rs2, label]) => Ok(Self::Blt {
                rs1: rs1.parse()?,
                rs2: rs2.parse()?,
                label: label.parse()?,
            }),
            ("bge" | "bgeu", [rs1, rs2, label]) => Ok(Self::Bge {
                rs1: rs1.parse()?,
                rs2: rs2.parse()?,
                label: label.parse()?,
            }),
            ("jal", [rd, label]) => Ok(Self::Jal {
                rd: rd.parse()?,
                label: label.parse()?,
            }),
            ("jalr", [rd, rs1, offset]) => Ok(Self::Jalr {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
                offset: offset.parse()?,
            }),
            ("addi", [rd, rs1, imm]) => Ok(Self::Addi {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
                imm: imm.parse()?,
            }),
            ("xori", [rd, rs1, imm]) => Ok(Self::Xori {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
                imm: imm.parse()?,
            }),
            ("andi", [rd, rs1, imm]) => Ok(Self::Andi {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
                imm: imm.parse()?,
            }),
            ("ori", [rd, rs1, imm]) => Ok(Self::Ori {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
                imm: imm.parse()?,
            }),
            ("ld", [rd, offset_rs1]) => {
                let (offset, rs1) = parse_offset_rs1(offset_rs1)?;
                Ok(Self::Ld {
                    rd: rd.parse()?,
                    offset: offset.parse()?,
                    rs1: rs1.parse()?,
                })
            }
            ("sd", [rs2, offset_rs1]) => {
                let (offset, rs1) = parse_offset_rs1(offset_rs1)?;
                Ok(Self::Sd {
                    rs2: rs2.parse()?,
                    offset: offset.parse()?,
                    rs1: rs1.parse()?,
                })
            }
            ("slti", [rd, rs1, imm]) => Ok(Self::Slti {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
                imm: imm.parse()?,
            }),
            ("lui", [rd, imm]) => Ok(Self::Lui {
                rd: rd.parse()?,
                imm: imm.parse()?,
            }),
            ("auipc", [rd, imm]) => Ok(Self::Auipc {
                rd: rd.parse()?,
                imm: imm.parse()?,
            }),
            ("nop", [""]) => Ok(Self::Nop),
            ("li", [rd, imm]) => Ok(Self::Li {
                rd: rd.parse()?,
                imm: imm.parse()?,
            }),
            ("mv", [rd, rs1]) => Ok(Self::Mv {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
            }),
            ("not", [rd, rs1]) => Ok(Self::Not {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
            }),
            ("neg", [rd, rs1]) => Ok(Self::Neg {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
            }),
            ("slt" | "sltu", [rd, rs1, rs2]) => Ok(Self::Slt {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
                rs2: rs2.parse()?,
            }),
            ("seqz", [rd, rs1]) => Ok(Self::Seqz {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
            }),
            ("snez", [rd, rs1]) => Ok(Self::Snez {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
            }),
            ("sltz", [rd, rs1]) => Ok(Self::Sltz {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
            }),
            ("sgtz", [rd, rs1]) => Ok(Self::Sgtz {
                rd: rd.parse()?,
                rs1: rs1.parse()?,
            }),
            ("beqz", [rs1, label]) => Ok(Self::Beqz {
                rs1: rs1.parse()?,
                label: label.parse()?,
            }),
            ("bnez", [rs1, label]) => Ok(Self::Bnez {
                rs1: rs1.parse()?,
                label: label.parse()?,
            }),
            ("blez", [rs1, label]) => Ok(Self::Blez {
                rs1: rs1.parse()?,
                label: label.parse()?,
            }),
            ("bgez", [rs1, label]) => Ok(Self::Bgez {
                rs1: rs1.parse()?,
                label: label.parse()?,
            }),
            ("bltz", [rs1, label]) => Ok(Self::Bltz {
                rs1: rs1.parse()?,
                label: label.parse()?,
            }),
            ("bgtz", [rs1, label]) => Ok(Self::Bgtz {
                rs1: rs1.parse()?,
                label: label.parse()?,
            }),
            ("bgt", [rs1, rs2, label]) => Ok(Self::Bgt {
                rs1: rs1.parse()?,
                rs2: rs2.parse()?,
                label: label.parse()?,
            }),
            ("ble", [rs1, rs2, label]) => Ok(Self::Ble {
                rs1: rs1.parse()?,
                rs2: rs2.parse()?,
                label: label.parse()?,
            }),
            ("j", [label]) => Ok(Self::J {
                label: label.parse()?,
            }),
            ("jr", [rs1]) => Ok(Self::Jr { rs1: rs1.parse()? }),
            ("call", [label]) => Ok(Self::Call {
                label: label.parse()?,
            }),
            ("ret", [""]) => Ok(Self::Ret),
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
            Instruction::Add { rd, rs1, rs2 } => write!(f, "add {rd},{rs1},{rs2}"),
            Instruction::Addi { rd, rs1, imm } => write!(f, "addi {rd},{rs1},{imm}"),
            Instruction::And { rd, rs1, rs2 } => write!(f, "and {rd},{rs1},{rs2}"),
            Instruction::Andi { rd, rs1, imm } => write!(f, "andi {rd},{rs1},{imm}"),
            Instruction::Auipc { rd, imm } => write!(f, "auipc {rd},{imm}"),
            Instruction::Beq { rs1, rs2, label } => write!(f, "beq {rs1},{rs2},{label}"),
            Instruction::Bge { rs1, rs2, label } => write!(f, "bge {rs1},{rs2},{label}"),
            Instruction::Blt { rs1, rs2, label } => write!(f, "blt {rs1},{rs2},{label}"),
            Instruction::Bne { rs1, rs2, label } => write!(f, "bne {rs1},{rs2},{label}"),
            Instruction::Jal { rd, label } => write!(f, "jal {rd},{label}"),
            Instruction::Jalr { rd, rs1, offset } => write!(f, "jalr {rd},{rs1},{offset}"),
            Instruction::Ld { rd, offset, rs1 } => write!(f, "ld {rd},{offset}({rs1})"),
            Instruction::Lui { rd, imm } => write!(f, "lui {rd},{imm}"),
            Instruction::Mul { rd, rs1, rs2 } => write!(f, "mul {rd},{rs1},{rs2}"),
            Instruction::Div { rd, rs1, rs2 } => write!(f, "div {rd},{rs1},{rs2}"),
            Instruction::Rem { rd, rs1, rs2 } => write!(f, "rem {rd},{rs1},{rs2}"),
            Instruction::Or { rd, rs1, rs2 } => write!(f, "or {rd},{rs1},{rs2}"),
            Instruction::Ori { rd, rs1, imm } => write!(f, "ori {rd},{rs1},{imm}"),
            Instruction::Sd { rs2, offset, rs1 } => write!(f, "sd {rs2},{offset}({rs1})"),
            Instruction::Sll { rd, rs1, rs2 } => write!(f, "sll {rd},{rs1},{rs2}"),
            Instruction::Slli { rd, rs1, shamt } => write!(f, "slli {rd},{rs1},{shamt}"),
            Instruction::Slti { rd, rs1, imm } => write!(f, "slti {rd},{rs1},{imm}"),
            Instruction::Srl { rd, rs1, rs2 } => write!(f, "srl {rd},{rs1},{rs2}"),
            Instruction::Srli { rd, rs1, shamt } => write!(f, "srli {rd},{rs1},{shamt}"),
            Instruction::Sub { rd, rs1, rs2 } => write!(f, "sub {rd},{rs1},{rs2}"),
            Instruction::Xor { rd, rs1, rs2 } => write!(f, "xor {rd},{rs1},{rs2}"),
            Instruction::Xori { rd, rs1, imm } => write!(f, "xori {rd},{rs1},{imm}"),
            Instruction::Nop => write!(f, "nop"),
            Instruction::Li { rd, imm } => write!(f, "li {rd},{imm}"),
            Instruction::Mv { rd, rs1 } => write!(f, "mv {rd},{rs1}"),
            Instruction::Not { rd, rs1 } => write!(f, "not {rd},{rs1}"),
            Instruction::Neg { rd, rs1 } => write!(f, "neg {rd},{rs1}"),
            Instruction::Slt { rd, rs1, rs2 } => write!(f, "slt {rd},{rs1},{rs2}"),
            Instruction::Seqz { rd, rs1 } => write!(f, "seqz {rd},{rs1}"),
            Instruction::Snez { rd, rs1 } => write!(f, "snez {rd},{rs1}"),
            Instruction::Sltz { rd, rs1 } => write!(f, "sltz {rd},{rs1}"),
            Instruction::Sgtz { rd, rs1 } => write!(f, "sgtz {rd},{rs1}"),
            Instruction::Beqz { rs1, label } => write!(f, "beqz {rs1},{label}"),
            Instruction::Bnez { rs1, label } => write!(f, "bnez {rs1},{label}"),
            Instruction::Blez { rs1, label } => write!(f, "blez {rs1},{label}"),
            Instruction::Bgez { rs1, label } => write!(f, "bgez {rs1},{label}"),
            Instruction::Bltz { rs1, label } => write!(f, "bltz {rs1},{label}"),
            Instruction::Bgtz { rs1, label } => write!(f, "bgtz {rs1},{label}"),
            Instruction::Bgt { rs1, rs2, label } => write!(f, "bgt {rs1},{rs2},{label}]"),
            Instruction::Ble { rs1, rs2, label } => write!(f, "ble {rs1},{rs2},{label}"),
            Instruction::J { label } => write!(f, "j {label}"),
            Instruction::Jr { rs1 } => write!(f, "jr {rs1}"),
            Instruction::Ret => write!(f, "ret"),
            Instruction::Call { label } => write!(f, "call {label}"),
            Instruction::Label(label) => write!(f, "{label}:"),
        }
    }
}

/// [`Program`] wrapper around [`Vec<Instruction>`]
#[derive(Debug, PartialEq, Eq)]
pub struct Program(pub Vec<Instruction>);

impl FromStr for Program {
    type Err = Error;

    fn from_str(s: &str) -> std::result::Result<Self, Self::Err> {
        let instructions = s
            .trim()
            .lines()
            .filter(|l| !l.starts_with('#') && !l.is_empty())
            .map(|l| l.trim().parse())
            .collect::<Result<Vec<Instruction>>>()?;
        Ok(Program(instructions))
    }
}

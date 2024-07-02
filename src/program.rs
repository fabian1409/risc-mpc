use crate::{
    error::{Error, Result},
    Instruction, Label,
};
use log::debug;
use std::{collections::HashMap, str::FromStr};

/// [`Program`] wrapper around [`Vec<Instruction>`]
#[derive(Debug, PartialEq, Eq)]
pub struct Program {
    pub(crate) instructions: Vec<Instruction>,
    pub(crate) entry: u64,
    pub(crate) text_labels: HashMap<String, u64>,
}

impl Program {
    /// Create a new [`Program`].
    pub fn new(instructions: Vec<Instruction>) -> Self {
        let mut text_labels = HashMap::new();
        for (i, instruction) in instructions.iter().enumerate() {
            if let Instruction::Label(Label::Text(name)) = instruction {
                text_labels.insert(name.clone(), i as u64);
            }
        }
        Self {
            instructions,
            entry: 0,
            text_labels,
        }
    }

    /// Add a entry point [`Program`] if execution should not start at offset 0.
    pub fn with_entry(mut self, entry: &str) -> Result<Self> {
        let entry_offset = self
            .text_labels
            .get(entry)
            .ok_or(Error::UnknownLabel(entry.to_string()))?;
        self.entry = *entry_offset;
        Ok(self)
    }

    /// Find the pc offset for a given [`Label`].
    pub fn offset(&self, label: &Label, pc: u64) -> Result<u64> {
        match label {
            Label::Text(name) => self
                .text_labels
                .get(name.trim_end_matches("@plt"))
                .copied()
                .ok_or(Error::UnknownLabel(name.to_string())),
            Label::Numeric(name) => {
                if name.ends_with('f') {
                    for (i, instruction) in self.instructions.iter().enumerate().skip(pc as usize) {
                        if let Instruction::Label(Label::Numeric(other)) = instruction {
                            if name.strip_suffix('f').unwrap().eq(other) {
                                debug!("found label = {} at pc = {}", other, i);
                                return Ok(i as u64);
                            }
                        }
                    }
                } else {
                    for (i, instruction) in
                        self.instructions.iter().take(pc as usize).rev().enumerate()
                    {
                        if let Instruction::Label(Label::Numeric(other)) = instruction {
                            if name.strip_suffix('b').unwrap().eq(other) {
                                debug!("found label = {} at pc = {}", other, i);
                                return Ok(i as u64);
                            }
                        }
                    }
                }
                Err(Error::UnknownLabel(name.to_string()))
            }
        }
    }
}

impl FromStr for Program {
    type Err = Error;

    fn from_str(s: &str) -> std::result::Result<Self, Self::Err> {
        let instructions = s
            .trim()
            .lines()
            .filter(|l| !l.starts_with('#') && !l.is_empty())
            .map(|l| l.trim())
            .map(|l| {
                // TODO this is a hack, maybe make instructions as var of Value and store them in mem to actually find the DWORDS there
                if let Some(pos) = l.find("%pcrel_hi(") {
                    let start = pos + "%pcrel_hi(".len();
                    let end = l[start..].find(')').unwrap() + start;
                    let label = &l[start..end];
                    l.replace(&("%pcrel_hi(".to_string() + label + ")"), label)
                } else if let Some(pos) = l.find("%pcrel_lo") {
                    let start = pos + "%pcrel_lo(".len();
                    let end = l[start..].find(')').unwrap() + start;
                    let label = &l[start..end];
                    let line = l
                        .replace(&("%pcrel_lo(".to_string() + label + ")"), "")
                        .replace(['(', ')'], "");
                    if l.starts_with("ld") {
                        line.replace("ld", "mv")
                    } else if l.starts_with("fld") {
                        line.replace("fld", "fmv.d.x")
                    } else {
                        panic!("unsupported assembler directive")
                    }
                } else if l.contains('%') {
                    panic!("unsupported assembler directive")
                } else {
                    l.to_string()
                }
            })
            .map(|l| l.parse())
            .collect::<Result<Vec<Instruction>>>()?;
        Ok(Program::new(instructions))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::XRegister;

    #[test]
    fn test_dword() {
        let program = "
            .LCPI2_0:
                    .quad   3787428097924915520
                    auipc   a0, %pcrel_hi(.LCPI2_0)
                    ld      a0, %pcrel_lo(.Lpcrel_hi0)(a0)
        "
        .parse::<Program>()
        .unwrap();

        assert_eq!(
            program.instructions,
            vec![
                Instruction::Label(Label::Text(".LCPI2_0".to_string())),
                Instruction::DWORD(3787428097924915520),
                Instruction::AUIPC {
                    rd: XRegister::x10,
                    label: Label::Text(".LCPI2_0".to_string())
                },
                Instruction::MV {
                    rd: XRegister::x10,
                    rs1: XRegister::x10,
                }
            ]
        );
    }
}

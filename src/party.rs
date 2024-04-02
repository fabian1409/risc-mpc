use crate::{
    channel::{Channel, Message},
    error::{Error, Result},
    instruction::{Instruction, Label, Program},
    memory::{Address, Memory},
    mpc_executor::{x_to_shares, MPCExecutor, ToFixedPoint},
    registers::{Register, Registers},
    triple_provider::TripleProvider,
    types::{Float, Input, Integer, Output, Value},
    Share, U64_BYTES,
};
use log::{debug, info};
use serde::{Deserialize, Serialize};
use std::{collections::HashMap, mem::take, ops::Range, time::Instant};

/// Id for party 0
pub const PARTY_0: usize = 0;
/// Id for party 1
pub const PARTY_1: usize = 1;

/// [`Location`] represents either a [`Register`] or a memory [`Address`].
///
/// [`Register`]: Location::Register
/// [`Address`]: Location::Address
#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub enum Location {
    Register(Register),
    Address(Address),
}

/// A [builder] used to instantiate a [`Party`] struct.
/// Use this builder to set registers and memory.
///
/// [builder]: https://rust-unofficial.github.io/patterns/patterns/creational/builder.html
#[derive(Debug)]
pub struct PartyBuilder<C: Channel> {
    id: usize,
    ch: C,
    registers: Registers,
    memory: Memory,
    secret_inputs: Vec<(Location, Value)>,
    n_mul_triples: u64,
    n_and_triples: u64,
}

impl<C: Channel> PartyBuilder<C> {
    /// Constructs a new [`PartyBuilder`].
    ///
    /// # Panics
    /// If `id` is not [`PARTY_0`] or [`PARTY_1`].
    pub fn new(id: usize, ch: C) -> PartyBuilder<C> {
        assert!(id == PARTY_0 || id == PARTY_1);
        PartyBuilder {
            id,
            ch,
            registers: Registers::new(),
            memory: Memory::new(),
            secret_inputs: Vec::new(),
            n_mul_triples: 0,
            n_and_triples: 0,
        }
    }

    /// Set a [`Register`] to a given [`Input`].
    pub fn register(mut self, register: Register, input: Input) -> PartyBuilder<C> {
        match input {
            Input::Integer(Integer::Public(x)) => {
                self.registers.set(register, Integer::Public(x).into())
            }
            Input::Integer(Integer::Secret(secret)) => {
                let (share0, share1) = x_to_shares(secret);
                self.registers.set(register, Integer::Secret(share0).into());
                self.secret_inputs
                    .push((Location::Register(register), Integer::Secret(share1).into()));
            }
            Input::Float(Float::Public(x)) => self.registers.set(register, Float::Public(x).into()),
            Input::Float(Float::Secret(secret)) => {
                let (share0, share1) = x_to_shares(Share::Arithmetic(secret));
                self.registers
                    .set(register, Float::Secret(share0.into()).into());
                self.secret_inputs.push((
                    Location::Register(register),
                    Float::Secret(share1.into()).into(),
                ));
            }
        }
        self
    }

    /// Set a [`Address`] to a given [`Input`].
    pub fn address(mut self, address: Address, input: Input) -> Result<PartyBuilder<C>> {
        match input {
            Input::Integer(Integer::Public(x)) => {
                self.memory.store(address, Integer::Public(x).into())?
            }
            Input::Integer(Integer::Secret(secret)) => {
                let (share0, share1) = x_to_shares(secret);
                self.memory.store(address, Integer::Secret(share0).into())?;
                self.secret_inputs
                    .push((Location::Address(address), Integer::Secret(share1).into()));
            }
            Input::Float(Float::Public(x)) => {
                self.memory.store(address, Float::Public(x).into())?
            }
            Input::Float(Float::Secret(secret)) => {
                let (share0, share1) = x_to_shares(Share::Arithmetic(secret));
                self.memory
                    .store(address, Float::Secret(share0.into()).into())?;
                self.secret_inputs.push((
                    Location::Address(address),
                    Float::Secret(share1.into()).into(),
                ));
            }
        }
        Ok(self)
    }

    /// Set a [`Address`] range to a given [`Vec<Input>`].
    /// The range is determined by the base `address` and ```inputs.len() * U64_BYTES```.
    pub fn address_range(
        mut self,
        address: Address,
        inputs: Vec<Input>,
    ) -> Result<PartyBuilder<C>> {
        for (i, input) in inputs.into_iter().enumerate() {
            let address = address + i as u64 * U64_BYTES;
            self = self.address(address, input)?;
        }
        Ok(self)
    }

    /// Set the number of multiplication triples to generate in the setup phase
    pub fn n_mul_triples(mut self, n: u64) -> PartyBuilder<C> {
        self.n_mul_triples = n;
        self
    }

    /// Set the number of and triples to generate in the setup phase
    pub fn n_and_triples(mut self, n: u64) -> PartyBuilder<C> {
        self.n_and_triples = n;
        self
    }

    /// Send all shares to other party
    fn send_secret_inputs(&mut self) -> Result<()> {
        debug!(
            "party {} sending {} inputs",
            self.id,
            self.secret_inputs.len()
        );
        self.ch
            .send(Message::SecretInputs(take(&mut self.secret_inputs)))?;
        Ok(())
    }

    // Receive shares from other party
    fn recv_secret_inputs(&mut self) -> Result<()> {
        debug!("party {} receiving inputs", self.id);
        if let Message::SecretInputs(secret_inputs) = self.ch.recv()? {
            for (location, value) in secret_inputs {
                match location {
                    Location::Register(register) => self.registers.set(register, value),
                    Location::Address(address) => self.memory.store(address, value)?,
                }
            }
        }
        Ok(())
    }

    /// Construct the [`Party`] instance.
    ///
    /// The setup phase is done in this function, so it can take a long time.
    /// Returned [`Party`] can be used to execute a [`Program`].
    pub fn build(mut self) -> Result<Party<C>> {
        if self.id == PARTY_0 {
            self.send_secret_inputs()?;
            self.recv_secret_inputs()?;
        } else {
            self.recv_secret_inputs()?;
            self.send_secret_inputs()?;
        }

        let mut triple_provider = TripleProvider::new(self.id);
        triple_provider.setup(&mut self.ch, self.n_mul_triples, self.n_and_triples)?;

        Ok(Party {
            id: self.id,
            registers: self.registers,
            memory: self.memory,
            pc: 0,
            call_depth: 0,
            executor: MPCExecutor::new(self.id, self.ch, triple_provider),
        })
    }
}

/// A [`Party`] instance with initialized registers and memory that is used to execute a [`Program`].
#[allow(unused)]
#[derive(Debug)]
pub struct Party<C: Channel> {
    id: usize,
    registers: Registers,
    memory: Memory,
    pc: u64,
    call_depth: u64,
    executor: MPCExecutor<C>,
}

impl<C: Channel> Party<C> {
    /// Open the secret value or get the public value as [`Output`] from the given [`Register`].
    pub fn register(&mut self, register: Register) -> Result<Output> {
        let value = self.registers.get(register);
        self.open(value)
    }

    /// Open the secret value (only for [`Party`] with given `id`) or get the public value as [`Output`] from the given [`Register`].
    pub fn register_for(&mut self, register: Register, id: usize) -> Result<Option<Output>> {
        let value = self.registers.get(register);
        self.open_for(value, id)
    }

    /// Open the secret value or get the public value as [`Output`] from the given [`Address`].
    pub fn address(&mut self, address: Address) -> Result<Output> {
        let value = self.memory.load(address)?;
        self.open(value)
    }

    /// Open the secret value (only for [`Party`] with given `id`) or get the public value as [`Output`] from the given [`Address`].
    pub fn address_for(&mut self, address: Address, id: usize) -> Result<Option<Output>> {
        let value = self.memory.load(address)?;
        self.open_for(value, id)
    }

    /// Open all secret values or get the public values in the given [`Range<Address>`].
    pub fn address_range(&mut self, range: Range<Address>) -> Result<Vec<Output>> {
        debug!("open address range = {range:?}");
        range
            .step_by(8)
            .map(|address| self.address(address))
            .collect()
    }

    /// Open all secret values or get the public values in the given [`Range<Address>`] only for [`Party`].
    pub fn address_range_for(
        &mut self,
        range: Range<Address>,
        id: usize,
    ) -> Result<Option<Vec<Output>>> {
        debug!("open address range = {range:?}");
        range
            .step_by(8)
            .map(|address| self.address_for(address, id))
            .collect()
    }

    fn open(&mut self, value: Value) -> Result<Output> {
        match value {
            Value::Integer(Integer::Public(x)) => Ok(x.into()),
            Value::Integer(Integer::Secret(share)) => self.executor.reveal(share).map(Output::from),
            Value::Float(Float::Public(x)) => Ok(x.into()),
            Value::Float(Float::Secret(share)) => Ok(self
                .executor
                .reveal(Share::Arithmetic(share))?
                .to_fixed_point()?
                .into()),
        }
    }

    fn open_for(&mut self, value: Value, id: usize) -> Result<Option<Output>> {
        match value {
            Value::Integer(Integer::Public(x)) => Ok(Some(x.into())),
            Value::Integer(Integer::Secret(share)) => {
                Ok(self.executor.reveal_for(share, id)?.map(Output::from))
            }
            Value::Float(Float::Public(x)) => Ok(Some(x.into())),
            Value::Float(Float::Secret(share)) => {
                if let Some(x) = self.executor.reveal_for(Share::Arithmetic(share), id)? {
                    Ok(Some(x.to_fixed_point()?.into()))
                } else {
                    Ok(None)
                }
            }
        }
    }

    /// Load the [`Value`] from the address given by `base + offset` and store in `dest`.
    fn load(&mut self, base: Register, offset: i32, dest: Register) -> Result<()> {
        if let Value::Integer(Integer::Public(base)) = self.registers.get(base) {
            let address = base + offset as u64;
            let value = self.memory.load(address)?;
            self.registers.set(dest, value);
            Ok(())
        } else {
            Err(Error::InvalidAddress)
        }
    }

    /// Store the [`Value`] from the `src` register at the address given by `base + offset`.
    fn store(&mut self, base: Register, offset: i32, src: Register) -> Result<()> {
        if let Value::Integer(Integer::Public(base)) = self.registers.get(base) {
            let address = base + offset as u64;
            let value = self.registers.get(src);
            self.memory.store(address, value)?;
            Ok(())
        } else {
            Err(Error::InvalidAddress)
        }
    }

    fn update_pc(&mut self, base: u64, offset: i32) {
        debug!("update_pc base = {base} offset = {offset}");
        if offset.is_negative() {
            self.pc = base - offset.unsigned_abs() as u64;
        } else {
            self.pc = base + offset as u64;
        }
    }

    /// Find the pc offset for a given [`Label`].
    fn offset(
        &self,
        label: &Label,
        text_labels: &HashMap<String, u64>,
        program: &[Instruction],
    ) -> Result<u64> {
        match label {
            Label::Text(name) => text_labels
                .get(name)
                .copied()
                .ok_or(Error::UnknownLabel(label.to_string())),
            Label::Numeric(name) => {
                if name.ends_with('f') {
                    for (i, instruction) in program.iter().enumerate().skip(self.pc as usize) {
                        if let Instruction::Label(Label::Numeric(other)) = instruction {
                            if name.strip_suffix('f').unwrap().eq(other) {
                                debug!("found label = {} at pc = {}", other, i);
                                return Ok(i as u64);
                            }
                        }
                    }
                } else {
                    for (i, instruction) in program.iter().take(self.pc as usize).rev().enumerate()
                    {
                        if let Instruction::Label(Label::Numeric(other)) = instruction {
                            if name.strip_suffix('b').unwrap().eq(other) {
                                debug!("found label = {} at pc = {}", other, i);
                                return Ok(i as u64);
                            }
                        }
                    }
                }
                Err(Error::UnknownLabel(label.to_string()))
            }
        }
    }

    /// Execute the given [`Program`].
    pub fn execute(&mut self, program: &Program) -> Result<()> {
        let start = Instant::now();
        let mut text_labels = HashMap::new();
        for (i, instruction) in program.0.iter().enumerate() {
            if let Instruction::Label(Label::Text(name)) = instruction {
                text_labels.insert(name.clone(), i as u64);
            }
        }

        while let Some(instruction) = program.0.get(self.pc as usize) {
            if !matches!(instruction, Instruction::Label(_)) {
                debug!("instruction = {instruction}");
            }
            match instruction {
                Instruction::ADDI { rd, rs1, imm } => {
                    let src = self.registers.get(*rs1).try_into()?;
                    let res = self.executor.addi(src, *imm)?;
                    debug!("addi res = {res:?}");
                    self.registers.set(*rd, res.into());
                }
                Instruction::ADD { rd, rs1, rs2 } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let rs2 = self.registers.get(*rs2).try_into()?;
                    let res = self.executor.add(rs1, rs2)?;
                    debug!("add res = {res:?}");
                    self.registers.set(*rd, res.into());
                }
                Instruction::SUB { rd, rs1, rs2 } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let rs2 = self.registers.get(*rs2).try_into()?;
                    let res = self.executor.sub(rs1, rs2)?;
                    debug!("sub res = {res:?}");
                    self.registers.set(*rd, res.into());
                }
                Instruction::DIV { rd, rs1, rs2 } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let rs2 = self.registers.get(*rs2).try_into()?;
                    let res = self.executor.div(rs1, rs2)?;
                    debug!("div res = {res:?}");
                    self.registers.set(*rd, res.into());
                }
                Instruction::REM { rd, rs1, rs2 } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let rs2 = self.registers.get(*rs2).try_into()?;
                    let res = self.executor.rem(rs1, rs2)?;
                    debug!("rem res = {res:?}");
                    self.registers.set(*rd, res.into());
                }
                Instruction::MUL { rd, rs1, rs2 } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let rs2 = self.registers.get(*rs2).try_into()?;
                    let res = self.executor.mul(rs1, rs2)?;
                    debug!("mul res = {res:?}");
                    self.registers.set(*rd, res.into());
                }
                Instruction::XOR { rd, rs1, rs2 } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let rs2 = self.registers.get(*rs2).try_into()?;
                    let res = self.executor.xor(rs1, rs2)?;
                    debug!("xor res = {res:?}");
                    self.registers.set(*rd, res.into());
                }
                Instruction::XORI { rd, rs1, imm } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let res = self.executor.xori(rs1, *imm)?;
                    debug!("xori res = {res:?}");
                    self.registers.set(*rd, res.into());
                }
                Instruction::AND { rd, rs1, rs2 } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let rs2 = self.registers.get(*rs2).try_into()?;
                    let res = self.executor.and(rs1, rs2)?;
                    debug!("and res = {res:?}");
                    self.registers.set(*rd, res.into());
                }
                Instruction::ANDI { rd, rs1, imm } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let res = self.executor.andi(rs1, *imm)?;
                    debug!("andi res = {res:?}");
                    self.registers.set(*rd, res.into());
                }
                Instruction::OR { rd, rs1, rs2 } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let rs2 = self.registers.get(*rs2).try_into()?;
                    let res = self.executor.or(rs1, rs2)?;
                    debug!("or res = {res:?}");
                    self.registers.set(*rd, res.into());
                }
                Instruction::ORI { rd, rs1, imm } => {
                    let src = self.registers.get(*rs1).try_into()?;
                    let res = self.executor.ori(src, *imm)?;
                    debug!("ori res = {res:?}");
                    self.registers.set(*rd, res.into());
                }
                Instruction::LD { rd, offset, rs1 } => {
                    self.load(*rs1, *offset, *rd)?;
                }
                Instruction::SD { rs2, offset, rs1 } => {
                    self.store(*rs1, *offset, *rs2)?;
                }
                Instruction::SLL { rd, rs1, rs2 } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let rs2 = self.registers.get(*rs2).try_into()?;
                    let res = self.executor.lshift(rs1, rs2)?;
                    debug!("sll res = {res:?}");
                    self.registers.set(*rd, res.into());
                }
                Instruction::SLLI { rd, rs1, shamt } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let res = self.executor.lshift(rs1, Integer::Public(*shamt as u64))?;
                    debug!("slli res = {res:?}");
                    self.registers.set(*rd, res.into());
                }
                Instruction::SRL { rd, rs1, rs2 } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let rs2 = self.registers.get(*rs2).try_into()?;
                    let res = self.executor.rshift(rs1, rs2)?;
                    debug!("srl res = {res:?}");
                    self.registers.set(*rd, res.into());
                }
                Instruction::SRLI { rd, rs1, shamt } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let res = self.executor.rshift(rs1, Integer::Public(*shamt as u64))?;
                    debug!("srli res = {res:?}");
                    self.registers.set(*rd, res.into());
                }
                Instruction::JAL { rd, label } => {
                    self.registers.set(*rd, Integer::Public(self.pc + 1).into());
                    let address = self.offset(label, &text_labels, &program.0)?;
                    self.update_pc(address, 0);
                }
                Instruction::JALR { rd, rs1, offset } => {
                    self.registers.set(*rd, Integer::Public(self.pc + 1).into());
                    let base = self.registers.get(*rs1);
                    if let Value::Integer(Integer::Public(base)) = base {
                        self.update_pc(base, *offset);
                    } else {
                        return Err(Error::InvalidAddress);
                    }
                }
                Instruction::BEQ { rs1, rs2, label } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let rs2 = self.registers.get(*rs2).try_into()?;
                    let eq = self.executor.beq(rs1, rs2)?;
                    if eq {
                        debug!("beq taking branch");
                        let address = self.offset(label, &text_labels, &program.0)?;
                        self.update_pc(address, 0);
                    }
                }
                Instruction::BNE { rs1, rs2, label } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let rs2 = self.registers.get(*rs2).try_into()?;
                    let eq = self.executor.beq(rs1, rs2)?;
                    if !eq {
                        debug!("bne taking branch");
                        let address = self.offset(label, &text_labels, &program.0)?;
                        self.update_pc(address, 0);
                    }
                }
                Instruction::BLT { rs1, rs2, label } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let rs2 = self.registers.get(*rs2).try_into()?;
                    let lt = self.executor.blt(rs1, rs2)?;
                    if lt {
                        debug!("blt taking branch");
                        let address = self.offset(label, &text_labels, &program.0)?;
                        self.update_pc(address, 0);
                    }
                }
                Instruction::BGE { rs1, rs2, label } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let rs2 = self.registers.get(*rs2).try_into()?;
                    let lt = self.executor.blt(rs1, rs2)?;
                    if !lt {
                        debug!("bge taking branch");
                        let address = self.offset(label, &text_labels, &program.0)?;
                        self.update_pc(address, 0);
                    }
                }
                Instruction::SLTI { rd, rs1, imm } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let res = self.executor.lt(rs1, Integer::Public(*imm as u64))?;
                    debug!("slti res = {res:?}");
                    self.registers.set(*rd, res.into());
                }
                Instruction::LUI { rd, imm } => {
                    self.registers
                        .set(*rd, Integer::Public((*imm as u64) << 12).into());
                }
                Instruction::AUIPC { rd, imm } => {
                    let address = if imm.is_negative() {
                        self.pc - ((imm.wrapping_abs() as u64) << 12)
                    } else {
                        self.pc + ((*imm as u64) << 12)
                    };
                    self.registers.set(*rd, Integer::Public(address).into());
                }
                Instruction::NOP => {}
                Instruction::LI { rd, imm } => {
                    self.registers.set(*rd, Integer::Public(*imm as u64).into());
                }
                Instruction::MV { rd, rs1 } => {
                    let rs1 = self.registers.get(*rs1);
                    self.registers.set(*rd, rs1);
                }
                Instruction::NOT { rd, rs1 } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let res = self.executor.xori(rs1, -1)?;
                    debug!("not res = {res:?}");
                    self.registers.set(*rd, res.into());
                }
                Instruction::NEG { rd, rs1 } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let res = self.executor.sub(Integer::Public(0), rs1)?;
                    debug!("neg res = {res:?}");
                    self.registers.set(*rd, res.into());
                }
                Instruction::SEQZ { rd, rs1 } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let res = self.executor.eq(rs1, Integer::Public(0))?;
                    debug!("seqz res = {res:?}");
                    self.registers
                        .set(*rd, Integer::Public(res.as_u64()).into());
                }
                Instruction::SNEZ { rd, rs1 } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let res = self.executor.neq(rs1, Integer::Public(0))?;
                    debug!("snez res = {res:?}");
                    self.registers.set(*rd, res.into());
                }
                Instruction::SLTZ { rd, rs1 } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let lt = self.executor.lt(rs1, Integer::Public(0))?;
                    debug!("sltz lt = {lt:?}");
                    self.registers.set(*rd, Integer::Public(lt.as_u64()).into());
                }
                Instruction::SLT { rd, rs1, rs2 } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let rs2 = self.registers.get(*rs2).try_into()?;
                    let lt = self.executor.lt(rs1, rs2)?;
                    debug!("slt lt = {lt:?}");
                    self.registers.set(*rd, Integer::Public(lt.as_u64()).into());
                }
                Instruction::SGTZ { rd, rs1 } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let gt = self.executor.gt(rs1, Integer::Public(0))?;
                    debug!("sgtz gt = {gt:?}");
                    self.registers.set(*rd, Integer::Public(gt.as_u64()).into());
                }
                Instruction::BEQZ { rs1, label } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let eq = self.executor.beq(rs1, Integer::Public(0))?;
                    if eq {
                        debug!("beqz taking branch");
                        let address = self.offset(label, &text_labels, &program.0)?;
                        self.update_pc(address, 0);
                    }
                }
                Instruction::BNEZ { rs1, label } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let eq = self.executor.beq(rs1, Integer::Public(0))?;
                    if !eq {
                        debug!("bnez taking branch");
                        let address = self.offset(label, &text_labels, &program.0)?;
                        self.update_pc(address, 0);
                    }
                }
                Instruction::BLEZ { rs1, label } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let le = self.executor.ble(rs1, Integer::Public(0))?;
                    if le {
                        debug!("blez taking branch");
                        let address = self.offset(label, &text_labels, &program.0)?;
                        self.update_pc(address, 0);
                    }
                }
                Instruction::BGEZ { rs1, label } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let ge = self.executor.bge(rs1, Integer::Public(0))?;
                    if ge {
                        debug!("bgez taking branch");
                        let address = self.offset(label, &text_labels, &program.0)?;
                        self.update_pc(address, 0);
                    }
                }
                Instruction::BLTZ { rs1, label } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let lt = self.executor.blt(rs1, Integer::Public(0))?;
                    if lt {
                        debug!("bltz taking branch");
                        let address = self.offset(label, &text_labels, &program.0)?;
                        self.update_pc(address, 0);
                    }
                }
                Instruction::BGTZ { rs1, label } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let gt = self.executor.bgt(rs1, Integer::Public(0))?;
                    if gt {
                        debug!("bgtz taking branch");
                        let address = self.offset(label, &text_labels, &program.0)?;
                        self.update_pc(address, 0);
                    }
                }
                Instruction::BGT { rs1, rs2, label } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let rs2 = self.registers.get(*rs2).try_into()?;
                    let gt = self.executor.bgt(rs1, rs2)?;
                    if gt {
                        debug!("bgt taking branch");
                        let address = self.offset(label, &text_labels, &program.0)?;
                        self.update_pc(address, 0);
                    }
                }
                Instruction::BLE { rs1, rs2, label } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let rs2 = self.registers.get(*rs2).try_into()?;
                    let le = self.executor.ble(rs1, rs2)?;
                    if le {
                        debug!("ble taking branch");
                        let address = self.offset(label, &text_labels, &program.0)?;
                        self.update_pc(address, 0);
                    }
                }
                Instruction::J { label } => {
                    let address = self.offset(label, &text_labels, &program.0)?;
                    self.update_pc(address, 0);
                }
                Instruction::JR { rs1 } => {
                    if let Value::Integer(Integer::Public(address)) = self.registers.get(*rs1) {
                        self.update_pc(address, 0);
                    } else {
                        return Err(Error::InvalidAddress);
                    }
                }
                Instruction::RET => {
                    if let Value::Integer(Integer::Public(address)) =
                        self.registers.get(Register::x1)
                    {
                        // ignore trailing ret if no calls were made
                        if self.call_depth > 0 {
                            self.update_pc(address, 0);
                            self.call_depth -= 1;
                        }
                    } else {
                        return Err(Error::InvalidAddress);
                    }
                }
                Instruction::CALL { label } => {
                    self.registers
                        .set(Register::x1, Integer::Public(self.pc).into());
                    let address = self.offset(label, &text_labels, &program.0)?;
                    self.update_pc(address, 0);
                    self.call_depth += 1;
                }
                Instruction::Label(_) => {}
            };
            self.update_pc(self.pc, 1);
        }
        let duration = start.elapsed();
        info!("execution done, took {}ms", duration.as_millis());
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std::{
        collections::BTreeSet,
        sync::mpsc::{self, Receiver, Sender},
        thread,
    };

    use super::{PartyBuilder, Register, PARTY_0};
    use crate::{
        channel::{Message, MockChannel, ThreadChannel},
        party::PARTY_1,
        Float, Integer, Output, Result, Share, U64_BYTES,
    };
    use approx::assert_relative_eq;

    fn mock_channel() -> MockChannel {
        let mut ch = MockChannel::new();
        ch.expect_send().returning(|_| Ok(()));
        ch.expect_recv()
            .returning(|| Ok(Message::SecretInputs(Vec::new())));
        ch
    }

    fn create_channels() -> (ThreadChannel, ThreadChannel) {
        let (tx0, rx0): (Sender<Message>, Receiver<Message>) = mpsc::channel();
        let (tx1, rx1): (Sender<Message>, Receiver<Message>) = mpsc::channel();
        let ch0 = ThreadChannel::new(tx0, rx1);
        let ch1 = ThreadChannel::new(tx1, rx0);
        (ch0, ch1)
    }

    #[test]
    fn factorial() -> Result<()> {
        // https://godbolt.org/z/ancndW5T4
        let program = "
            example::factorial:
                    mv      a1, a0
                    li      a0, 1
                    li      a2, 2
                    bltu    a1, a2, .LBB0_2
            .LBB0_1:
                    addi    a3, a1, -1
                    mul     a0, a1, a0
                    mv      a1, a3
                    bgeu    a3, a2, .LBB0_1
            .LBB0_2:
                    ret
        "
        .parse()?;

        let mut party = PartyBuilder::new(PARTY_0, mock_channel())
            .register(Register::x10, Integer::Public(5).into())
            .build()?;
        party.execute(&program)?;
        let res = party.register(Register::x10)?.to_u64()?;

        assert_eq!(res, 120); // 5!
        Ok(())
    }

    #[test]
    fn mean() -> Result<()> {
        // https://godbolt.org/z/MM14WjcGY
        let program = "
            example::mean:
                    slli    a2, a1, 3
                    fmv.d.x fa5, zero
                    beqz    a2, .LBB0_2
            .LBB0_1:
                    fld     fa4, 0(a0)
                    addi    a0, a0, 8
                    fadd.d  fa5, fa5, fa4
                    addi    a2, a2, -8
                    bnez    a2, .LBB0_1
            .LBB0_2:
                    fcvt.d.lu       fa4, a1
                    fdiv.d  fa0, fa5, fa4
                    ret
        "
        .parse()?;

        let mut party = PartyBuilder::new(PARTY_0, mock_channel())
            .register(Register::x10, Integer::Public(0x0).into())
            .register(Register::x10, Integer::Public(3).into())
            .address_range(
                0x0,
                vec![
                    Float::Public(2.0).into(),
                    Float::Public(3.5).into(),
                    Float::Public(1.5).into(),
                ],
            )?
            .build()?;
        party.execute(&program)?;
        let res = party.register(Register::x10)?.to_f64()?;

        assert_relative_eq!(res, 3.5, epsilon = 10e-3);
        Ok(())
    }

    #[test]
    fn fibonacci() -> Result<()> {
        // https://godbolt.org/z/8ezr3fbMM
        let program = "
            example::fibonacci:
                    addi    sp, sp, -32
                    sd      ra, 24(sp)
                    sd      s0, 16(sp)
                    sd      s1, 8(sp)
                    sd      s2, 0(sp)
                    mv      s0, a0
                    li      s1, 0
                    li      s2, 2
                    bltu    a0, s2, .LBB0_2
            .LBB0_1:
                    addi    a0, s0, -1
                    call    example::fibonacci
                    add     s1, s1, a0
                    addi    s0, s0, -2
                    bgeu    s0, s2, .LBB0_1
            .LBB0_2:
                    add     a0, s0, s1
                    ld      ra, 24(sp)
                    ld      s0, 16(sp)
                    ld      s1, 8(sp)
                    ld      s2, 0(sp)
                    addi    sp, sp, 32
                    ret
        "
        .parse()?;

        let mut party = PartyBuilder::new(PARTY_0, mock_channel())
            .register(Register::x10, Integer::Public(10).into())
            .build()?;
        party.execute(&program)?;
        let res = party.register(Register::x10)?.to_u64()?;

        assert_eq!(res, 55); // fib(10)
        Ok(())
    }

    #[test]
    fn private_set_intersection() -> Result<()> {
        // https://godbolt.org/z/98jq1r3j1
        let program = "
            example::psi:
                    li      a6, 0
                    li      a7, 0
                    li      t1, 0
            .LBB0_1:
                    slli    t0, a7, 3
                    add     t0, t0, a2
                    slli    t2, t1, 3
                    add     t2, t2, a0
            .LBB0_2:
                    sltu    t3, a7, a3
                    sltu    a5, t1, a1
                    and     a5, a5, t3
                    beqz    a5, .LBB0_8
                    ld      t3, 0(t2)
                    ld      a5, 0(t0)
                    bgeu    t3, a5, .LBB0_5
                    addi    t1, t1, 1
                    addi    t2, t2, 8
                    j       .LBB0_2
            .LBB0_5:
                    bgeu    a5, t3, .LBB0_7
                    addi    a7, a7, 1
                    j       .LBB0_1
            .LBB0_7:
                    addi    t1, t1, 1
                    addi    a7, a7, 1
                    slli    a5, a6, 3
                    add     a5, a5, a4
                    sd      t3, 0(a5)
                    addi    a6, a6, 1
                    j       .LBB0_1
            .LBB0_8:
                    mv      a0, a6
                    ret
        ";

        let (ch0, ch1) = create_channels();

        let set0 = BTreeSet::from([1, 2, 3]);
        let set1 = BTreeSet::from([2, 3, 4]);
        let set0_len = set0.len() as u64;
        let set1_len = set1.len() as u64;
        let intersection = set0.intersection(&set1).copied().collect::<Vec<u64>>();

        let base_address = 0x0;
        let set0_address = base_address;
        let set1_address = base_address + U64_BYTES * set0_len;
        let intersection_addr = set1_address + U64_BYTES * set1_len;

        let run = move |id: usize,
                        ch: ThreadChannel,
                        set: BTreeSet<u64>,
                        set_address: u64|
              -> Result<Vec<u64>> {
            let mut party = PartyBuilder::new(id, ch)
                .register(Register::x10, Integer::Public(set0_address).into())
                .register(Register::x11, Integer::Public(set0_len).into())
                .register(Register::x12, Integer::Public(set1_address).into())
                .register(Register::x13, Integer::Public(set1_len).into())
                .register(Register::x14, Integer::Public(intersection_addr).into())
                .address_range(
                    set_address,
                    set.iter()
                        .map(|x| Integer::Secret(Share::Arithmetic(*x)).into())
                        .collect(),
                )?
                .build()?;

            party.execute(&program.parse()?)?;

            let len = party.register(Register::x10)?.to_u64()?;

            party
                .address_range(intersection_addr..intersection_addr + U64_BYTES * len)?
                .into_iter()
                .map(Output::to_u64)
                .collect::<Result<Vec<u64>>>()
        };

        let party0 = thread::spawn(move || run(PARTY_0, ch0, set0, set0_address));
        let party1 = thread::spawn(move || run(PARTY_1, ch1, set1, set1_address));

        let intersection0 = party0.join().unwrap().unwrap();
        let intersection1 = party1.join().unwrap().unwrap();

        assert_eq!(intersection0, intersection);
        assert_eq!(intersection1, intersection);

        Ok(())
    }
}

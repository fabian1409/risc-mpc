use crate::{
    channel::{Channel, Message},
    error::{Error, Result},
    instruction::Instruction,
    memory::{Address, Memory},
    mpc_executor::{x_to_shares, MPCExecutor, ToFixedPoint},
    program::Program,
    registers::{Register, Registers},
    triple_provider::TripleProvider,
    types::{Float, Input, Integer, Output, Value},
    Share, U64_BYTES,
};
use log::{debug, info};
use serde::{Deserialize, Serialize};
use std::{mem::take, ops::Range, time::Instant};

/// Id for party 0
pub const PARTY_0: usize = 0;
/// Id for party 1
pub const PARTY_1: usize = 1;

/// [`Location`] represents either a [`Register`] or a memory [`Address`].
///
/// [`Register`]: Location::Register
/// [`Address`]: Location::Address
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq, Hash, PartialOrd, Ord)]
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
                self.registers.set(register, Integer::Public(x).into());
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
                self.memory.store(address, Integer::Public(x).into())?;
            }
            Input::Integer(Integer::Secret(secret)) => {
                let (share0, share1) = x_to_shares(secret);
                self.memory.store(address, Integer::Secret(share0).into())?;
                self.secret_inputs
                    .push((Location::Address(address), Integer::Secret(share1).into()));
            }
            Input::Float(Float::Public(x)) => {
                self.memory.store(address, Float::Public(x).into())?;
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

        let mut triple_provider = TripleProvider::new(self.id, &mut self.ch)?;
        if self.n_mul_triples > 0 || self.n_and_triples > 0 {
            triple_provider.setup(&mut self.ch, self.n_mul_triples, self.n_and_triples)?;
        }

        Ok(Party {
            id: self.id,
            registers: self.registers,
            memory: self.memory,
            pc: 0,
            call_depth: 0,
            executor: MPCExecutor::new(self.id, self.ch, triple_provider)?,
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
        if let Integer::Public(base) = self.registers.get(base).try_into()? {
            let address = base + offset as u64;
            let value = self.memory.load(address)?;
            self.registers.set(dest, value);
            Ok(())
        } else {
            Err(Error::SecretValueAsAddress)
        }
    }

    /// Store the [`Value`] from the `src` register at the address given by `base + offset`.
    fn store(&mut self, base: Register, offset: i32, src: Register) -> Result<()> {
        if let Integer::Public(base) = self.registers.get(base).try_into()? {
            let address = base + offset as u64;
            let value = self.registers.get(src);
            self.memory.store(address, value)?;
            Ok(())
        } else {
            Err(Error::SecretValueAsAddress)
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

    /// Execute the given [`Program`].
    pub fn execute(&mut self, program: &Program) -> Result<()> {
        let start = Instant::now();
        let instructions = &program.instructions;
        self.pc = program.entry_offset;

        while let Some(instruction) = instructions.get(self.pc as usize) {
            if !matches!(instruction, Instruction::Label(_)) {
                debug!("instruction = {instruction}");
            }
            match instruction {
                Instruction::ADDI { rd, rs1, imm } => {
                    let src = self.registers.get(*rs1).try_into()?;
                    let res = self.executor.addi(src, *imm)?.into();
                    debug!("addi res = {res:?}");
                    self.registers.set(*rd, res);
                }
                Instruction::ADD { rd, rs1, rs2 } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let rs2 = self.registers.get(*rs2).try_into()?;
                    let res = self.executor.add(rs1, rs2)?.into();
                    debug!("add res = {res:?}");
                    self.registers.set(*rd, res);
                }
                Instruction::SUB { rd, rs1, rs2 } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let rs2 = self.registers.get(*rs2).try_into()?;
                    let res = self.executor.sub(rs1, rs2)?.into();
                    debug!("sub res = {res:?}");
                    self.registers.set(*rd, res);
                }
                Instruction::DIV { rd, rs1, rs2 } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let rs2 = self.registers.get(*rs2).try_into()?;
                    let res = self.executor.div(rs1, rs2)?.into();
                    debug!("div res = {res:?}");
                    self.registers.set(*rd, res);
                }
                Instruction::REM { rd, rs1, rs2 } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let rs2 = self.registers.get(*rs2).try_into()?;
                    let res = self.executor.rem(rs1, rs2)?.into();
                    debug!("rem res = {res:?}");
                    self.registers.set(*rd, res);
                }
                Instruction::MUL { rd, rs1, rs2 } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let rs2 = self.registers.get(*rs2).try_into()?;
                    let res = self.executor.mul(rs1, rs2)?.into();
                    debug!("mul res = {res:?}");
                    self.registers.set(*rd, res);
                }
                Instruction::XOR { rd, rs1, rs2 } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let rs2 = self.registers.get(*rs2).try_into()?;
                    let res = self.executor.xor(rs1, rs2)?.into();
                    debug!("xor res = {res:?}");
                    self.registers.set(*rd, res);
                }
                Instruction::XORI { rd, rs1, imm } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let res = self.executor.xori(rs1, *imm)?.into();
                    debug!("xori res = {res:?}");
                    self.registers.set(*rd, res);
                }
                Instruction::AND { rd, rs1, rs2 } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let rs2 = self.registers.get(*rs2).try_into()?;
                    let res = self.executor.and(rs1, rs2)?.into();
                    debug!("and res = {res:?}");
                    self.registers.set(*rd, res);
                }
                Instruction::ANDI { rd, rs1, imm } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let res = self.executor.andi(rs1, *imm)?.into();
                    debug!("andi res = {res:?}");
                    self.registers.set(*rd, res);
                }
                Instruction::OR { rd, rs1, rs2 } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let rs2 = self.registers.get(*rs2).try_into()?;
                    let res = self.executor.or(rs1, rs2)?.into();
                    debug!("or res = {res:?}");
                    self.registers.set(*rd, res);
                }
                Instruction::ORI { rd, rs1, imm } => {
                    let src = self.registers.get(*rs1).try_into()?;
                    let res = self.executor.ori(src, *imm)?.into();
                    debug!("ori res = {res:?}");
                    self.registers.set(*rd, res);
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
                    let res = self.executor.lshift(rs1, rs2)?.into();
                    debug!("sll res = {res:?}");
                    self.registers.set(*rd, res);
                }
                Instruction::SLLI { rd, rs1, shamt } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let res = self
                        .executor
                        .lshift(rs1, Integer::Public(*shamt as u64))?
                        .into();
                    debug!("slli res = {res:?}");
                    self.registers.set(*rd, res);
                }
                Instruction::SRL { rd, rs1, rs2 } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let rs2 = self.registers.get(*rs2).try_into()?;
                    let res = self.executor.rshift(rs1, rs2)?.into();
                    debug!("srl res = {res:?}");
                    self.registers.set(*rd, res);
                }
                Instruction::SRLI { rd, rs1, shamt } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let res = self
                        .executor
                        .rshift(rs1, Integer::Public(*shamt as u64))?
                        .into();
                    debug!("srli res = {res:?}");
                    self.registers.set(*rd, res);
                }
                Instruction::JAL { rd, label } => {
                    self.registers.set(*rd, Integer::Public(self.pc + 1).into());
                    let address = program.offset(label, self.pc)?;
                    self.update_pc(address, 0);
                    self.call_depth += 1;
                }
                Instruction::JALR { rd, rs1, offset } => {
                    self.registers.set(*rd, Integer::Public(self.pc + 1).into());
                    let base = self.registers.get(*rs1);
                    if let Integer::Public(base) = base.try_into()? {
                        self.update_pc(base, *offset);
                        self.call_depth += 1;
                    } else {
                        return Err(Error::SecretValueAsAddress);
                    }
                }
                Instruction::BEQ { rs1, rs2, label } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let rs2 = self.registers.get(*rs2).try_into()?;
                    let eq = self.executor.beq(rs1, rs2)?;
                    if eq {
                        debug!("beq taking branch");
                        let address = program.offset(label, self.pc)?;
                        self.update_pc(address, 0);
                    }
                }
                Instruction::BNE { rs1, rs2, label } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let rs2 = self.registers.get(*rs2).try_into()?;
                    let eq = self.executor.beq(rs1, rs2)?;
                    if !eq {
                        debug!("bne taking branch");
                        let address = program.offset(label, self.pc)?;
                        self.update_pc(address, 0);
                    }
                }
                Instruction::BLT { rs1, rs2, label } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let rs2 = self.registers.get(*rs2).try_into()?;
                    let lt = self.executor.blt(rs1, rs2)?;
                    if lt {
                        debug!("blt taking branch");
                        let address = program.offset(label, self.pc)?;
                        self.update_pc(address, 0);
                    }
                }
                Instruction::BGE { rs1, rs2, label } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let rs2 = self.registers.get(*rs2).try_into()?;
                    let lt = self.executor.blt(rs1, rs2)?;
                    if !lt {
                        debug!("bge taking branch");
                        let address = program.offset(label, self.pc)?;
                        self.update_pc(address, 0);
                    }
                }
                Instruction::SLTI { rd, rs1, imm } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let res = self.executor.lt(rs1, Integer::Public(*imm as u64))?.into();
                    debug!("slti res = {res:?}");
                    self.registers.set(*rd, res);
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
                    let res = self.executor.xori(rs1, -1)?.into();
                    debug!("not res = {res:?}");
                    self.registers.set(*rd, res);
                }
                Instruction::NEG { rd, rs1 } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let res = self.executor.sub(Integer::Public(0), rs1)?.into();
                    debug!("neg res = {res:?}");
                    self.registers.set(*rd, res);
                }
                Instruction::SEQZ { rd, rs1 } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let res = self.executor.eq(rs1, Integer::Public(0))?.into();
                    debug!("seqz res = {res:?}");
                    self.registers.set(*rd, res);
                }
                Instruction::SNEZ { rd, rs1 } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let res = self.executor.neq(rs1, Integer::Public(0))?.into();
                    debug!("snez res = {res:?}");
                    self.registers.set(*rd, res);
                }
                Instruction::SLTZ { rd, rs1 } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let lt = self.executor.lt(rs1, Integer::Public(0))?.into();
                    debug!("sltz lt = {lt:?}");
                    self.registers.set(*rd, lt);
                }
                Instruction::SLT { rd, rs1, rs2 } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let rs2 = self.registers.get(*rs2).try_into()?;
                    let lt = self.executor.lt(rs1, rs2)?.into();
                    debug!("slt lt = {lt:?}");
                    self.registers.set(*rd, lt);
                }
                Instruction::SGTZ { rd, rs1 } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let gt = self.executor.gt(rs1, Integer::Public(0))?.into();
                    debug!("sgtz gt = {gt:?}");
                    self.registers.set(*rd, gt);
                }
                Instruction::BEQZ { rs1, label } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let eq = self.executor.beq(rs1, Integer::Public(0))?;
                    if eq {
                        debug!("beqz taking branch");
                        let address = program.offset(label, self.pc)?;
                        self.update_pc(address, 0);
                    }
                }
                Instruction::BNEZ { rs1, label } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let eq = self.executor.beq(rs1, Integer::Public(0))?;
                    if !eq {
                        debug!("bnez taking branch");
                        let address = program.offset(label, self.pc)?;
                        self.update_pc(address, 0);
                    }
                }
                Instruction::BLEZ { rs1, label } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let le = self.executor.ble(rs1, Integer::Public(0))?;
                    if le {
                        debug!("blez taking branch");
                        let address = program.offset(label, self.pc)?;
                        self.update_pc(address, 0);
                    }
                }
                Instruction::BGEZ { rs1, label } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let ge = self.executor.bge(rs1, Integer::Public(0))?;
                    if ge {
                        debug!("bgez taking branch");
                        let address = program.offset(label, self.pc)?;
                        self.update_pc(address, 0);
                    }
                }
                Instruction::BLTZ { rs1, label } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let lt = self.executor.blt(rs1, Integer::Public(0))?;
                    if lt {
                        debug!("bltz taking branch");
                        let address = program.offset(label, self.pc)?;
                        self.update_pc(address, 0);
                    }
                }
                Instruction::BGTZ { rs1, label } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let gt = self.executor.bgt(rs1, Integer::Public(0))?;
                    if gt {
                        debug!("bgtz taking branch");
                        let address = program.offset(label, self.pc)?;
                        self.update_pc(address, 0);
                    }
                }
                Instruction::BGT { rs1, rs2, label } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let rs2 = self.registers.get(*rs2).try_into()?;
                    let gt = self.executor.bgt(rs1, rs2)?;
                    if gt {
                        debug!("bgt taking branch");
                        let address = program.offset(label, self.pc)?;
                        self.update_pc(address, 0);
                    }
                }
                Instruction::BLE { rs1, rs2, label } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let rs2 = self.registers.get(*rs2).try_into()?;
                    let le = self.executor.ble(rs1, rs2)?;
                    if le {
                        debug!("ble taking branch");
                        let address = program.offset(label, self.pc)?;
                        self.update_pc(address, 0);
                    }
                }
                Instruction::J { label } => {
                    debug!("jump to {label}");
                    let address = program.offset(label, self.pc)?;
                    self.update_pc(address, 0);
                }
                Instruction::JR { rs1 } => {
                    if let Integer::Public(address) = self.registers.get(*rs1).try_into()? {
                        debug!("jump to {address}");
                        self.update_pc(address, 0);
                    } else {
                        return Err(Error::SecretValueAsAddress);
                    }
                }
                Instruction::RET => {
                    if let Integer::Public(address) = self.registers.get(Register::x1).try_into()? {
                        // ignore trailing ret if no calls were made
                        if self.call_depth > 0 {
                            self.update_pc(address, 0);
                            self.call_depth -= 1;
                        } else {
                            break;
                        }
                    } else {
                        return Err(Error::SecretValueAsAddress);
                    }
                }
                Instruction::CALL { label } => {
                    let address = program.offset(label, self.pc)?;
                    self.registers
                        .set(Register::x1, Integer::Public(self.pc).into());
                    self.update_pc(address, 0);
                    self.call_depth += 1;
                }
                Instruction::TAIL { label } => {
                    // same as call but dont write return address to x1
                    let address = program.offset(label, self.pc)?;
                    self.update_pc(address, 0);
                    self.call_depth += 1;
                }
                Instruction::Label(_) => {}
                Instruction::FADD { rd, rs1, rs2 } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let rs2 = self.registers.get(*rs2).try_into()?;
                    let res = self.executor.fadd(rs1, rs2)?;
                    debug!("fadd res = {res:?}");
                    self.registers.set(*rd, res.into());
                }
                Instruction::FSUB { rd, rs1, rs2 } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let rs2 = self.registers.get(*rs2).try_into()?;
                    let res = self.executor.fsub(rs1, rs2)?;
                    debug!("fsub res = {res:?}");
                    self.registers.set(*rd, res.into());
                }
                Instruction::FMUL { rd, rs1, rs2 } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let rs2 = self.registers.get(*rs2).try_into()?;
                    let res = self.executor.fmul(rs1, rs2)?;
                    debug!("fmul res = {res:?}");
                    self.registers.set(*rd, res.into());
                }
                Instruction::FDIV { rd, rs1, rs2 } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let rs2 = self.registers.get(*rs2).try_into()?;
                    let res = self.executor.fdiv(rs1, rs2)?;
                    debug!("fdiv res = {res:?}");
                    self.registers.set(*rd, res.into());
                }
                Instruction::FMIN { rd, rs1, rs2 } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let rs2 = self.registers.get(*rs2).try_into()?;
                    let res = self.executor.fmin(rs1, rs2)?;
                    debug!("fmin res = {res:?}");
                    self.registers.set(*rd, res.into());
                }
                Instruction::FMAX { rd, rs1, rs2 } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let rs2 = self.registers.get(*rs2).try_into()?;
                    let res = self.executor.fmax(rs1, rs2)?;
                    debug!("fmax res = {res:?}");
                    self.registers.set(*rd, res.into());
                }
                Instruction::FSQRT { rd, rs1 } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let res = self.executor.fsqrt(rs1)?;
                    debug!("fsqrt res = {res:?}");
                    self.registers.set(*rd, res.into());
                }
                Instruction::FLD { rd, offset, rs1 } => {
                    self.load(*rs1, *offset, *rd)?;
                }
                Instruction::FSD { rs2, offset, rs1 } => {
                    self.store(*rs1, *offset, *rs2)?;
                }
                Instruction::FMADD { rd, rs1, rs2, rs3 } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let rs2 = self.registers.get(*rs2).try_into()?;
                    let rs3 = self.registers.get(*rs3).try_into()?;
                    let res = self.executor.fmul(rs1, rs2)?;
                    let res = self.executor.fadd(res, rs3)?;
                    debug!("fmadd res = {res:?}");
                    self.registers.set(*rd, res.into());
                }
                Instruction::FMSUB { rd, rs1, rs2, rs3 } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let rs2 = self.registers.get(*rs2).try_into()?;
                    let rs3 = self.registers.get(*rs3).try_into()?;
                    let res = self.executor.fmul(rs1, rs2)?;
                    let res = self.executor.fsub(res, rs3)?;
                    debug!("fmsub res = {res:?}");
                    self.registers.set(*rd, res.into());
                }
                Instruction::FNMADD { rd, rs1, rs2, rs3 } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let rs2 = self.registers.get(*rs2).try_into()?;
                    let rs3 = self.registers.get(*rs3).try_into()?;
                    let res = self.executor.fmul(rs1, rs2)?;
                    let res = self.executor.fadd(res, rs3)?;
                    let res = self.executor.fsub(Float::Public(0.0), res)?;
                    debug!("fnmadd res = {res:?}");
                    self.registers.set(*rd, res.into());
                }
                Instruction::FNMSUB { rd, rs1, rs2, rs3 } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let rs2 = self.registers.get(*rs2).try_into()?;
                    let rs3 = self.registers.get(*rs3).try_into()?;
                    let res = self.executor.fmul(rs1, rs2)?;
                    let res = self.executor.fsub(res, rs3)?;
                    let res = self.executor.fsub(Float::Public(0.0), res)?;
                    debug!("fnmsub res = {res:?}");
                    self.registers.set(*rd, res.into());
                }
                Instruction::FCVTLUD { rd, rs1 } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let res = self.executor.fcvtlud(rs1)?;
                    self.registers.set(*rd, res.into());
                }
                Instruction::FCVTDLU { rd, rs1 } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let res = self.executor.fcvtdlu(rs1)?;
                    self.registers.set(*rd, res.into());
                }
                Instruction::FMV { rd, rs1 } => {
                    let rs1 = self.registers.get(*rs1);
                    self.registers.set(*rd, rs1);
                }
                Instruction::FMVXD { rd, rs1 } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    match rs1 {
                        Float::Public(x) => {
                            self.registers.set(*rd, Integer::Public(x.to_bits()).into())
                        }
                        Float::Secret(_) => todo!("secret float to integer"),
                    }
                }
                Instruction::FMVDX { rd, rs1 } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    match rs1 {
                        Integer::Public(x) => self
                            .registers
                            .set(*rd, Float::Public(f64::from_bits(x)).into()),
                        Integer::Secret(_) => todo!("secret integer to float"),
                    }
                }
                Instruction::FSGNJ { rd, rs1, rs2 } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let rs2 = self.registers.get(*rs2).try_into()?;
                    let res = self.executor.fsgnj(rs1, rs2)?;
                    debug!("fsgnj res = {res:?}");
                    self.registers.set(*rd, res.into());
                }
                Instruction::FSGNJN { rd, rs1, rs2 } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let rs2 = self.registers.get(*rs2).try_into()?;
                    let res = self.executor.fsgnjn(rs1, rs2)?;
                    debug!("fsgnjn res = {res:?}");
                    self.registers.set(*rd, res.into());
                }
                Instruction::FSGNJX { rd, rs1, rs2 } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let rs2 = self.registers.get(*rs2).try_into()?;
                    let res = self.executor.fsgnjx(rs1, rs2)?;
                    debug!("fsgnjx res = {res:?}");
                    self.registers.set(*rd, res.into());
                }
                Instruction::FEQ { rd, rs1, rs2 } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let rs2 = self.registers.get(*rs2).try_into()?;
                    let eq = self.executor.feq(rs1, rs2)?;
                    debug!("feq = {eq:?}");
                    self.registers.set(*rd, eq.into());
                }
                Instruction::FLT { rd, rs1, rs2 } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let rs2 = self.registers.get(*rs2).try_into()?;
                    let lt = self.executor.flt(rs1, rs2)?;
                    debug!("flt = {lt:?}");
                    self.registers.set(*rd, lt.into());
                }
                Instruction::FLE { rd, rs1, rs2 } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let rs2 = self.registers.get(*rs2).try_into()?;
                    let le = self.executor.fle(rs1, rs2)?;
                    debug!("fle = {le:?}");
                    self.registers.set(*rd, le.into());
                }
                Instruction::FCLASS { rd, rs1 } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let class = match rs1 {
                        Float::Public(x) => {
                            if x == f64::NEG_INFINITY {
                                1u64 << 0
                            } else if x.is_sign_negative() && x.is_normal() {
                                1u64 << 1
                            } else if x.is_sign_negative() && x.is_subnormal() {
                                1u64 << 2
                            } else if x.is_sign_negative() && x == -0.0 {
                                1u64 << 3
                            } else if x.is_sign_positive() && x == 0.0 {
                                1u64 << 4
                            } else if x.is_sign_positive() && x.is_subnormal() {
                                1u64 << 5
                            } else if x.is_sign_positive() && x.is_normal() {
                                1u64 << 6
                            } else if x == f64::INFINITY {
                                1u64 << 7
                            } else if x.is_nan() {
                                1u64 << 8
                            } else {
                                0
                            }
                        }
                        _ => todo!("class of secret float"),
                    };
                    debug!("fclass class = {class:?}");
                    self.registers.set(*rd, Integer::Public(class).into());
                }
                Instruction::FNEG { rd, rs1 } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let sign_rs1 = self.executor.fsign(rs1)?;
                    let sign = self.executor.sub(Integer::Public(0), sign_rs1)?;
                    let abs_rs1 = self.executor.fabs(rs1)?;
                    let res = self.executor.fmul_integer(abs_rs1, sign)?;
                    debug!("fneg res = {res:?}");
                    self.registers.set(*rd, res.into());
                }
                Instruction::FABS { rd, rs1 } => {
                    let rs1 = self.registers.get(*rs1).try_into()?;
                    let res = self.executor.fabs(rs1)?;
                    debug!("fabs res = {res:?}");
                    self.registers.set(*rd, res.into());
                }
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
    use super::{PartyBuilder, Register, PARTY_0};
    use crate::{
        channel::{Message, ThreadChannel},
        party::PARTY_1,
        types::Integer,
        Result, Share, U64_BYTES,
    };
    use std::{
        collections::BTreeSet,
        sync::mpsc::{self, Receiver, Sender},
        thread,
    };

    fn create_channels() -> (ThreadChannel, ThreadChannel) {
        let (tx0, rx0): (Sender<Message>, Receiver<Message>) = mpsc::channel();
        let (tx1, rx1): (Sender<Message>, Receiver<Message>) = mpsc::channel();
        let ch0 = ThreadChannel::new(tx0, rx1);
        let ch1 = ThreadChannel::new(tx1, rx0);
        (ch0, ch1)
    }

    #[test]
    fn factorial() -> Result<()> {
        // https://godbolt.org/z/3jb4EfhPW
        let program = "
            factorial:
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
        ";

        let (ch0, ch1) = create_channels();
        let run = move |id: usize, ch: ThreadChannel| -> Result<u64> {
            let mut party = PartyBuilder::new(id, ch)
                .register(Register::x10, Integer::Public(5).into())
                .build()?;
            party.execute(&program.parse()?)?;
            party.register(Register::x10)?.try_into()
        };

        let party0 = thread::spawn(move || run(PARTY_0, ch0));
        let party1 = thread::spawn(move || run(PARTY_1, ch1));

        let res0 = party0.join().unwrap().unwrap();
        let res1 = party1.join().unwrap().unwrap();

        assert_eq!(res0, 120); // 5!
        assert_eq!(res1, 120);

        Ok(())
    }

    #[test]
    fn fibonacci() -> Result<()> {
        // https://godbolt.org/z/r78zGvc9v
        let program = "
            fibonacci:
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
                    call    fibonacci
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
        ";

        let (ch0, ch1) = create_channels();
        let run = move |id: usize, ch: ThreadChannel| -> Result<u64> {
            let mut party = PartyBuilder::new(id, ch)
                .register(Register::x10, Integer::Public(10).into())
                .build()?;
            party.execute(&program.parse()?)?;
            party.register(Register::x10)?.try_into()
        };

        let party0 = thread::spawn(move || run(PARTY_0, ch0));
        let party1 = thread::spawn(move || run(PARTY_1, ch1));

        let res0 = party0.join().unwrap().unwrap();
        let res1 = party1.join().unwrap().unwrap();

        assert_eq!(res0, 55); // fib(10)
        assert_eq!(res1, 55);

        Ok(())
    }

    #[test]
    fn private_set_intersection() -> Result<()> {
        // https://godbolt.org/z/zjcPTzr8W
        let program = "
            psi:
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
        let intersection: Vec<u64> = set0.intersection(&set1).copied().collect();

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

            let len: u64 = party.register(Register::x10)?.try_into()?;

            party
                .address_range(intersection_addr..intersection_addr + U64_BYTES * len)?
                .into_iter()
                .map(TryInto::try_into)
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

    #[test]
    fn mean_salary() -> Result<()> {
        // https://godbolt.org/z/nGWWb5bbn
        let program = "
            mean:
                    addi    sp, sp, -16
                    sd      ra, 8(sp)
                    li      a6, 0
                    slli    a5, a1, 3
                    beqz    a5, .LBB0_2
            .LBB0_1:
                    ld      a4, 0(a0)
                    addi    a0, a0, 8
                    add     a6, a6, a4
                    addi    a5, a5, -8
                    bnez    a5, .LBB0_1
            .LBB0_2:
                    slli    a0, a3, 3
                    beqz    a0, .LBB0_4
            .LBB0_3:
                    ld      a4, 0(a2)
                    addi    a2, a2, 8
                    add     a6, a6, a4
                    addi    a0, a0, -8
                    bnez    a0, .LBB0_3
            .LBB0_4:
                    add     a1, a1, a3
                    beqz    a1, .LBB0_6
                    divu    a0, a6, a1
                    ld      ra, 8(sp)
                    addi    sp, sp, 16
                    ret
            .LBB0_6:
        ";

        let (ch0, ch1) = create_channels();

        let salaries0 = [1000, 2500, 1900, 3000, 2750, 5000];
        let salaries1 = [1200, 3500, 900, 4000, 1750, 1000];
        let salaries0_len = salaries0.len() as u64;
        let salaries1_len = salaries1.len() as u64;
        let mean =
            salaries0.iter().chain(salaries1.iter()).sum::<u64>() / (salaries0_len + salaries1_len);

        let base_address = 0x0;
        let salaries0_address = base_address;
        let salaries1_address = base_address + U64_BYTES * salaries0_len;

        let run = move |id: usize,
                        ch: ThreadChannel,
                        salaries: &[u64],
                        salaries_address: u64|
              -> Result<u64> {
            let mut party = PartyBuilder::new(id, ch)
                .register(Register::x10, Integer::Public(salaries0_address).into())
                .register(Register::x11, Integer::Public(salaries0_len).into())
                .register(Register::x12, Integer::Public(salaries1_address).into())
                .register(Register::x13, Integer::Public(salaries1_len).into())
                .address_range(
                    salaries_address,
                    salaries
                        .iter()
                        .map(|x| Integer::Secret(Share::Arithmetic(*x)).into())
                        .collect(),
                )?
                .build()?;

            party.execute(&program.parse()?)?;

            party.register(Register::x10)?.try_into()
        };

        let party0 = thread::spawn(move || run(PARTY_0, ch0, &salaries0, salaries0_address));
        let party1 = thread::spawn(move || run(PARTY_1, ch1, &salaries1, salaries1_address));

        let mean0 = party0.join().unwrap().unwrap();
        let mean1 = party1.join().unwrap().unwrap();

        assert!(mean0.abs_diff(mean) <= 1);
        assert!(mean1.abs_diff(mean) <= 1);

        Ok(())
    }

    #[test]
    fn ascon() -> Result<()> {
        // https://godbolt.org/z/T6PbP55E6
        let program = "
            round:
                ld      a6, 0(a1)
                ld      t0, 32(a1)
                ld      a7, 16(a1)
                ld      a3, 8(a1)
                ld      a1, 24(a1)
                xor     a5, t0, a6
                xor     a2, a7, a2
                xor     a6, a2, a3
                xor     a7, a1, t0
                not     a4, a3
                and     a2, a2, a4
                xor     t2, a2, a5
                not     a4, a6
                and     t1, a1, a4
                not     a4, a1
                and     a4, t0, a4
                xor     t3, a4, a6
                not     a2, a7
                and     a2, a2, a5
                xor     a1, a1, a2
                not     a2, a5
                and     a2, a2, a3
                xor     t0, a7, a2
                xor     a3, a3, t2
                xor     a2, t1, a3
                xor     a7, a1, t3
                xor     a1, t0, t2
                srli    a6, a1, 9
                slli    a5, a1, 55
                or      a5, a5, a6
                xor     a6, a5, a1
                srli    a5, a2, 22
                slli    a3, a2, 42
                or      a3, a3, a5
                xor     t1, a3, a2
                srli    a5, t3, 5
                slli    a4, t3, 59
                or      a4, a4, a5
                xor     a4, a4, t3
                srli    a5, a7, 7
                slli    a3, a7, 57
                or      a3, a3, a5
                xor     t2, a3, a7
                srli    a5, t0, 34
                slli    a3, t0, 30
                or      a3, a3, a5
                xor     t4, a3, t0
                srli    a5, a6, 19
                slli    a6, a6, 45
                or      a5, a6, a5
                xor     a1, a1, a5
                srli    a5, t1, 39
                slli    t1, t1, 25
                or      a5, t1, a5
                xor     a2, a2, a5
                srli    a5, a4, 1
                slli    a4, a4, 63
                or      a4, a4, a5
                xor     a4, t3, a4
                not     a4, a4
                srli    a5, t2, 10
                slli    t2, t2, 54
                or      a5, t2, a5
                xor     a5, a5, a7
                srli    a3, t4, 7
                slli    t4, t4, 57
                or      a3, t4, a3
                xor     a3, a3, t0
                sd      a1, 0(a0)
                sd      a2, 8(a0)
                sd      a4, 16(a0)
                sd      a5, 24(a0)
                sd      a3, 32(a0)
                ret
        ";

        let (ch0, ch1) = create_channels();
        let run = move |id: usize, ch: ThreadChannel| -> Result<Vec<u64>> {
            let mut party = if id == PARTY_0 {
                PartyBuilder::new(id, ch)
                    .register(Register::x10, Integer::Public(0x0).into())
                    .register(Register::x11, Integer::Public(U64_BYTES * 5).into())
                    .register(Register::x12, Integer::Public(0x1f).into())
                    .address_range(
                        U64_BYTES * 5,
                        vec![
                            Integer::Secret(Share::Binary(0x0123456789abcdef)).into(),
                            Integer::Secret(Share::Binary(0x23456789abcdef01)).into(),
                            Integer::Secret(Share::Binary(0x456789abcdef0123)).into(),
                            Integer::Secret(Share::Binary(0x6789abcdef012345)).into(),
                            Integer::Secret(Share::Binary(0x89abcde01234567f)).into(),
                        ],
                    )?
                    .build()?
            } else {
                PartyBuilder::new(id, ch)
                    .register(Register::x10, Integer::Public(0x0).into())
                    .register(Register::x11, Integer::Public(U64_BYTES * 5).into())
                    .register(Register::x12, Integer::Public(0x1f).into())
                    .build()?
            };
            party.execute(&program.parse()?)?;
            party
                .address_range(0x0..U64_BYTES * 5)?
                .into_iter()
                .map(TryInto::try_into)
                .collect::<Result<Vec<u64>>>()
        };

        let party0 = thread::spawn(move || run(PARTY_0, ch0));
        let party1 = thread::spawn(move || run(PARTY_1, ch1));

        let res0 = party0.join().unwrap().unwrap();
        let res1 = party1.join().unwrap().unwrap();

        // https://github.com/RustCrypto/sponges/blob/master/ascon/src/lib.rs
        let expected = [
            0x3c1748c9be2892ce,
            0x5eafb305cd26164f,
            0xf9470254bb3a4213,
            0xf0428daf0c5d3948,
            0x281375af0b294899,
        ];

        assert_eq!(res0, expected);
        assert_eq!(res1, expected);

        Ok(())
    }
}

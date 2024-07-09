use crate::{
    channel::{Channel, Message},
    error::{Error, Result},
    instruction::Instruction,
    memory::{Address, Memory},
    mpc_executor::{x_to_shares, MPCExecutor, ToFixedPoint},
    program::Program,
    registers::{FRegisters, Register, VRegisters, XRegister, XRegisters},
    triple_provider::TripleProvider,
    types::{Float, Integer, Value},
    FRegister, Label, Share, U64_BYTES,
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
    x_registers: XRegisters,
    f_registers: FRegisters,
    v_registers: VRegisters,
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
            x_registers: XRegisters::new(),
            f_registers: FRegisters::new(),
            v_registers: VRegisters::new(),
            memory: Memory::new(),
            secret_inputs: Vec::new(),
            n_mul_triples: 0,
            n_and_triples: 0,
        }
    }

    /// Set a [`XRegister`] to a given [`Integer`].
    pub fn register_u64(mut self, register: XRegister, integer: Integer) -> PartyBuilder<C> {
        match integer {
            Integer::Secret(secret) => {
                let (share0, share1) = x_to_shares(secret);
                self.x_registers.set(register, Integer::Secret(share0));
                self.secret_inputs.push((
                    Location::Register(register.into()),
                    Integer::Secret(share1).into(),
                ));
            }
            Integer::Public(_) => self.x_registers.set(register, integer),
        }
        self
    }

    /// Set a [`FRegister`] to a given [`Float`].
    pub fn register_f64(mut self, register: FRegister, float: Float) -> PartyBuilder<C> {
        match float {
            Float::Secret(secret) => {
                let (share0, share1) = x_to_shares(Share::Arithmetic(secret));
                self.f_registers.set(register, Float::Secret(share0.into()));
                self.secret_inputs.push((
                    Location::Register(register.into()),
                    Float::Secret(share1.into()).into(),
                ));
            }
            Float::Public(_) => self.f_registers.set(register, float),
        }
        self
    }

    /// Set a [`Address`] to a given [`Integer`].
    pub fn address_u64(mut self, address: Address, integer: Integer) -> Result<PartyBuilder<C>> {
        match integer {
            Integer::Secret(secret) => {
                let (share0, share1) = x_to_shares(secret);
                self.memory.store(address, Integer::Secret(share0).into())?;
                self.secret_inputs
                    .push((Location::Address(address), Integer::Secret(share1).into()));
            }
            Integer::Public(_) => self.memory.store(address, integer.into())?,
        }
        Ok(self)
    }

    /// Set a [`Address`] to a given [`Float`].
    pub fn address_f64(mut self, address: Address, float: Float) -> Result<PartyBuilder<C>> {
        match float {
            Float::Secret(secret) => {
                let (share0, share1) = x_to_shares(Share::Arithmetic(secret));
                self.memory
                    .store(address, Float::Secret(share0.into()).into())?;
                self.secret_inputs.push((
                    Location::Address(address),
                    Float::Secret(share1.into()).into(),
                ));
            }
            Float::Public(_) => self.memory.store(address, float.into())?,
        }
        Ok(self)
    }

    /// Set a [`Address`] range to a given [`Vec<Integer>`].
    /// The range is determined by the base `address` and ```inputs.len() * U64_BYTES```.
    pub fn address_range_u64(
        mut self,
        address: Address,
        integers: Vec<Integer>,
    ) -> Result<PartyBuilder<C>> {
        for (i, integer) in integers.into_iter().enumerate() {
            let address = address + i as u64 * U64_BYTES;
            self = self.address_u64(address, integer)?;
        }
        Ok(self)
    }

    /// Set a [`Address`] range to a given [`Vec<Float>`].
    /// The range is determined by the base `address` and ```inputs.len() * U64_BYTES```.
    pub fn address_range_f64(
        mut self,
        address: Address,
        floats: Vec<Float>,
    ) -> Result<PartyBuilder<C>> {
        for (i, float) in floats.into_iter().enumerate() {
            let address = address + i as u64 * U64_BYTES;
            self = self.address_f64(address, float)?;
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
                    Location::Register(register) => match value {
                        Value::Integer(integer) => {
                            self.x_registers.set(register.try_into()?, integer)
                        }
                        Value::Float(float) => self.f_registers.set(register.try_into()?, float),
                    },
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
            x_registers: self.x_registers,
            f_registers: self.f_registers,
            v_registers: self.v_registers,
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
    x_registers: XRegisters,
    f_registers: FRegisters,
    v_registers: VRegisters,
    memory: Memory,
    pc: u64,
    call_depth: u64,
    executor: MPCExecutor<C>,
}

impl<C: Channel> Party<C> {
    /// Open secret value or get public value as [`u64`] in given [`Register`].
    pub fn register_u64(&mut self, register: XRegister) -> Result<u64> {
        match self.x_registers.get(register) {
            Integer::Public(x) => Ok(x),
            Integer::Secret(share) => self.executor.reveal(share),
        }
    }

    /// Open secret value (only for [`Party`] with given `id`) or get public value as [`Option<u64>`] in given [`Register`].
    /// Other party will receive [`None`].
    pub fn register_for_u64(&mut self, register: XRegister, id: usize) -> Result<Option<u64>> {
        match self.x_registers.get(register) {
            Integer::Public(x) => Ok(Some(x)),
            Integer::Secret(share) => self.executor.reveal_for(share, id),
        }
    }

    /// Open secret value or get public value as [`f64`] in given [`Register`].
    pub fn register_f64(&mut self, register: FRegister) -> Result<f64> {
        match self.f_registers.get(register) {
            Float::Public(f) => Ok(f),
            Float::Secret(share) => self
                .executor
                .reveal(Share::Arithmetic(share))?
                .to_fixed_point(),
        }
    }

    /// Open secret value (only for [`Party`] with given `id`) or get public value as [`Option<f64>`] in given [`Register`].
    /// Other party will receive [`None`].
    pub fn register_for_f64(&mut self, register: FRegister, id: usize) -> Result<Option<f64>> {
        match self.f_registers.get(register) {
            Float::Public(f) => Ok(Some(f)),
            Float::Secret(share) => self
                .executor
                .reveal_for(Share::Arithmetic(share), id)?
                .map(ToFixedPoint::to_fixed_point)
                .transpose(),
        }
    }

    /// Open secret value or get public value as [`u64`] at given [`Address`].
    pub fn address_u64(&mut self, address: Address) -> Result<u64> {
        match self.memory.load(address)? {
            Value::Integer(Integer::Public(x)) => Ok(x),
            Value::Integer(Integer::Secret(share)) => self.executor.reveal(share),
            _ => Err(Error::UnexpectedValue),
        }
    }

    /// Open secret value (only for [`Party`] with given `id`) or get public value as [`Option<u64>`] at given [`Address`].
    /// Other party will receive [`None`].
    pub fn address_for_u64(&mut self, address: Address, id: usize) -> Result<Option<u64>> {
        match self.memory.load(address)? {
            Value::Integer(Integer::Public(x)) => Ok(Some(x)),
            Value::Integer(Integer::Secret(share)) => self.executor.reveal_for(share, id),
            _ => Err(Error::UnexpectedValue),
        }
    }

    /// Open secret value or get public value as [`f64`] at given [`Address`].
    pub fn address_f64(&mut self, address: Address) -> Result<f64> {
        match self.memory.load(address)? {
            Value::Float(Float::Public(f)) => Ok(f),
            Value::Float(Float::Secret(share)) => self
                .executor
                .reveal(Share::Arithmetic(share))?
                .to_fixed_point(),
            _ => Err(Error::UnexpectedValue),
        }
    }

    /// Open secret value (only for [`Party`] with given `id`) or get public value as [`Option<f64>`] at given [`Address`].
    /// Other party will receive [`None`].
    pub fn address_for_f64(&mut self, address: Address, id: usize) -> Result<Option<f64>> {
        match self.memory.load(address)? {
            Value::Float(Float::Public(f)) => Ok(Some(f)),
            Value::Float(Float::Secret(share)) => self
                .executor
                .reveal_for(Share::Arithmetic(share), id)?
                .map(ToFixedPoint::to_fixed_point)
                .transpose(),
            _ => Err(Error::UnexpectedValue),
        }
    }

    /// Open all secret values or get public values in given [`Range<Address>`] as [`Vec<u64>`].
    pub fn address_range_u64(&mut self, range: Range<Address>) -> Result<Vec<u64>> {
        debug!("open address range = {range:?}");
        range
            .step_by(8)
            .map(|address| self.address_u64(address))
            .collect()
    }

    /// Open all secret values (only for [`Party`] with given `id`) or get public values in given [`Range<Address>`] as [`Vec<u64>`].
    /// Other party will receive [`None`].
    pub fn address_range_u64_for(
        &mut self,
        range: Range<Address>,
        id: usize,
    ) -> Result<Option<Vec<u64>>> {
        debug!("open address range = {range:?}");
        range
            .step_by(8)
            .map(|address| self.address_for_u64(address, id))
            .collect()
    }

    /// Open all secret values or get public values in given [`Range<Address>`] as [`Vec<f64>`].
    pub fn address_range_f64(&mut self, range: Range<Address>) -> Result<Vec<f64>> {
        debug!("open address range = {range:?}");
        range
            .step_by(8)
            .map(|address| self.address_f64(address))
            .collect()
    }

    /// Open all secret values (only for [`Party`] with given `id`) or get public values in given [`Range<Address>`] as [`Vec<f64>`].
    /// Other party will receive [`None`].
    pub fn address_range_for_f64(
        &mut self,
        range: Range<Address>,
        id: usize,
    ) -> Result<Option<Vec<f64>>> {
        debug!("open address range = {range:?}");
        range
            .step_by(8)
            .map(|address| self.address_for_f64(address, id))
            .collect()
    }

    /// Execute the given [`Program`].
    pub fn execute(&mut self, program: &Program) -> Result<()> {
        let start = Instant::now();
        let instructions = &program.instructions;
        self.pc = program.entry;

        while let Some(instruction) = instructions.get(self.pc as usize) {
            if !matches!(instruction, Instruction::Label(_)) {
                debug!("instruction = {instruction}");
            }
            match instruction {
                Instruction::ADDI { rd, rs1, imm } => {
                    let src = self.x_registers.get(*rs1);
                    let res = self.executor.addi(src, *imm)?;
                    debug!("addi res = {res:?}");
                    self.x_registers.set(*rd, res);
                }
                Instruction::ADD { rd, rs1, rs2 } => {
                    let rs1 = self.x_registers.get(*rs1);
                    let rs2 = self.x_registers.get(*rs2);
                    let res = self.executor.add(rs1, rs2)?;
                    debug!("add res = {res:?}");
                    self.x_registers.set(*rd, res);
                }
                Instruction::SUB { rd, rs1, rs2 } => {
                    let rs1 = self.x_registers.get(*rs1);
                    let rs2 = self.x_registers.get(*rs2);
                    let res = self.executor.sub(rs1, rs2)?;
                    debug!("sub res = {res:?}");
                    self.x_registers.set(*rd, res);
                }
                Instruction::DIV { rd, rs1, rs2 } => {
                    let rs1 = self.x_registers.get(*rs1);
                    let rs2 = self.x_registers.get(*rs2);
                    let res = self.executor.div(rs1, rs2)?;
                    debug!("div res = {res:?}");
                    self.x_registers.set(*rd, res);
                }
                Instruction::REM { rd, rs1, rs2 } => {
                    let rs1 = self.x_registers.get(*rs1);
                    let rs2 = self.x_registers.get(*rs2);
                    let res = self.executor.rem(rs1, rs2)?;
                    debug!("rem res = {res:?}");
                    self.x_registers.set(*rd, res);
                }
                Instruction::MUL { rd, rs1, rs2 } => {
                    let rs1 = self.x_registers.get(*rs1);
                    let rs2 = self.x_registers.get(*rs2);
                    let res = self.executor.mul(rs1, rs2)?;
                    debug!("mul res = {res:?}");
                    self.x_registers.set(*rd, res);
                }
                Instruction::XOR { rd, rs1, rs2 } => {
                    let rs1 = self.x_registers.get(*rs1);
                    let rs2 = self.x_registers.get(*rs2);
                    let res = self.executor.xor(rs1, rs2)?;
                    debug!("xor res = {res:?}");
                    self.x_registers.set(*rd, res);
                }
                Instruction::XORI { rd, rs1, imm } => {
                    let rs1 = self.x_registers.get(*rs1);
                    let res = self.executor.xori(rs1, *imm)?;
                    debug!("xori res = {res:?}");
                    self.x_registers.set(*rd, res);
                }
                Instruction::AND { rd, rs1, rs2 } => {
                    let rs1 = self.x_registers.get(*rs1);
                    let rs2 = self.x_registers.get(*rs2);
                    let res = self.executor.and(rs1, rs2)?;
                    debug!("and res = {res:?}");
                    self.x_registers.set(*rd, res);
                }
                Instruction::ANDI { rd, rs1, imm } => {
                    let rs1 = self.x_registers.get(*rs1);
                    let res = self.executor.andi(rs1, *imm)?;
                    debug!("andi res = {res:?}");
                    self.x_registers.set(*rd, res);
                }
                Instruction::OR { rd, rs1, rs2 } => {
                    let rs1 = self.x_registers.get(*rs1);
                    let rs2 = self.x_registers.get(*rs2);
                    let res = self.executor.or(rs1, rs2)?;
                    debug!("or res = {res:?}");
                    self.x_registers.set(*rd, res);
                }
                Instruction::ORI { rd, rs1, imm } => {
                    let src = self.x_registers.get(*rs1);
                    let res = self.executor.ori(src, *imm)?;
                    debug!("ori res = {res:?}");
                    self.x_registers.set(*rd, res);
                }
                Instruction::LD { rd, offset, rs1 } => {
                    let base = self
                        .x_registers
                        .get(*rs1)
                        .as_public()
                        .ok_or(Error::SecretValueAsAddress)?;
                    let address = base + *offset as u64;
                    let value = self.memory.load(address)?;
                    self.x_registers.set(*rd, value.try_into()?);
                }
                Instruction::SD { rs2, offset, rs1 } => {
                    let base = self
                        .x_registers
                        .get(*rs1)
                        .as_public()
                        .ok_or(Error::SecretValueAsAddress)?;
                    let address = base + *offset as u64;
                    let value = self.x_registers.get(*rs2).into();
                    self.memory.store(address, value)?;
                }
                Instruction::SLL { rd, rs1, rs2 } => {
                    let rs1 = self.x_registers.get(*rs1);
                    let rs2 = self.x_registers.get(*rs2);
                    let res = self.executor.lshift(rs1, rs2)?;
                    debug!("sll res = {res:?}");
                    self.x_registers.set(*rd, res);
                }
                Instruction::SLLI { rd, rs1, shamt } => {
                    let rs1 = self.x_registers.get(*rs1);
                    let res = self.executor.lshift(rs1, Integer::Public(*shamt as u64))?;
                    debug!("slli res = {res:?}");
                    self.x_registers.set(*rd, res);
                }
                Instruction::SRL { rd, rs1, rs2 } => {
                    let rs1 = self.x_registers.get(*rs1);
                    let rs2 = self.x_registers.get(*rs2);
                    let res = self.executor.rshift(rs1, rs2)?;
                    debug!("srl res = {res:?}");
                    self.x_registers.set(*rd, res);
                }
                Instruction::SRLI { rd, rs1, shamt } => {
                    let rs1 = self.x_registers.get(*rs1);
                    let res = self.executor.rshift(rs1, Integer::Public(*shamt as u64))?;
                    debug!("srli res = {res:?}");
                    self.x_registers.set(*rd, res);
                }
                Instruction::JAL { rd, label } => {
                    self.x_registers.set(*rd, Integer::Public(self.pc + 1));
                    self.pc = program.offset(label, self.pc)?;
                    self.call_depth += 1;
                }
                Instruction::JALR { rd, rs1, offset } => {
                    self.x_registers.set(*rd, Integer::Public(self.pc + 1));
                    let base = self.x_registers.get(*rs1);
                    if let Integer::Public(base) = base {
                        self.pc = if offset.is_positive() {
                            base + offset.unsigned_abs() as u64
                        } else {
                            base - offset.unsigned_abs() as u64
                        };
                        self.call_depth += 1;
                    } else {
                        return Err(Error::SecretValueAsAddress);
                    }
                }
                Instruction::BEQ { rs1, rs2, label } => {
                    let rs1 = self.x_registers.get(*rs1);
                    let rs2 = self.x_registers.get(*rs2);
                    let eq = self.executor.beq(rs1, rs2)?;
                    if eq {
                        debug!("beq taking branch");
                        self.pc = program.offset(label, self.pc)?;
                    }
                }
                Instruction::BNE { rs1, rs2, label } => {
                    let rs1 = self.x_registers.get(*rs1);
                    let rs2 = self.x_registers.get(*rs2);
                    let eq = self.executor.beq(rs1, rs2)?;
                    if !eq {
                        debug!("bne taking branch");
                        self.pc = program.offset(label, self.pc)?;
                    }
                }
                Instruction::BLT { rs1, rs2, label } => {
                    let rs1 = self.x_registers.get(*rs1);
                    let rs2 = self.x_registers.get(*rs2);
                    let lt = self.executor.blt(rs1, rs2)?;
                    if lt {
                        debug!("blt taking branch");
                        self.pc = program.offset(label, self.pc)?;
                    }
                }
                Instruction::BGE { rs1, rs2, label } => {
                    let rs1 = self.x_registers.get(*rs1);
                    let rs2 = self.x_registers.get(*rs2);
                    let lt = self.executor.blt(rs1, rs2)?;
                    if !lt {
                        debug!("bge taking branch");
                        self.pc = program.offset(label, self.pc)?;
                    }
                }
                Instruction::SLTI { rd, rs1, imm } => {
                    let rs1 = self.x_registers.get(*rs1);
                    let res = self.executor.lt(rs1, Integer::Public(*imm as u64))?;
                    debug!("slti res = {res:?}");
                    self.x_registers.set(*rd, res);
                }
                Instruction::LUI { rd, imm } => {
                    self.x_registers
                        .set(*rd, Integer::Public((*imm as u64) << 12));
                }
                Instruction::AUIPC { rd, label } => {
                    let offset = program.offset(label, self.pc)?;
                    if let Some(Instruction::DWORD(dword)) =
                        program.instructions.get(offset as usize + 1)
                    {
                        self.x_registers.set(*rd, Integer::Public(*dword));
                    }
                }
                Instruction::NOP => {}
                Instruction::LI { rd, imm } => {
                    self.x_registers.set(*rd, Integer::Public(*imm as u64));
                }
                Instruction::MV { rd, rs1 } => {
                    let rs1 = self.x_registers.get(*rs1);
                    self.x_registers.set(*rd, rs1);
                }
                Instruction::NOT { rd, rs1 } => {
                    let rs1 = self.x_registers.get(*rs1);
                    let res = self.executor.xori(rs1, -1)?;
                    debug!("not res = {res:?}");
                    self.x_registers.set(*rd, res);
                }
                Instruction::NEG { rd, rs1 } => {
                    let rs1 = self.x_registers.get(*rs1);
                    let res = self.executor.sub(Integer::Public(0), rs1)?;
                    debug!("neg res = {res:?}");
                    self.x_registers.set(*rd, res);
                }
                Instruction::SEQZ { rd, rs1 } => {
                    let rs1 = self.x_registers.get(*rs1);
                    let res = self.executor.eq(rs1, Integer::Public(0))?;
                    debug!("seqz res = {res:?}");
                    self.x_registers.set(*rd, res);
                }
                Instruction::SNEZ { rd, rs1 } => {
                    let rs1 = self.x_registers.get(*rs1);
                    let res = self.executor.neq(rs1, Integer::Public(0))?;
                    debug!("snez res = {res:?}");
                    self.x_registers.set(*rd, res);
                }
                Instruction::SLTZ { rd, rs1 } => {
                    let rs1 = self.x_registers.get(*rs1);
                    let lt = self.executor.lt(rs1, Integer::Public(0))?;
                    debug!("sltz lt = {lt:?}");
                    self.x_registers.set(*rd, lt);
                }
                Instruction::SLT { rd, rs1, rs2 } => {
                    let rs1 = self.x_registers.get(*rs1);
                    let rs2 = self.x_registers.get(*rs2);
                    let lt = self.executor.lt(rs1, rs2)?;
                    debug!("slt lt = {lt:?}");
                    self.x_registers.set(*rd, lt);
                }
                Instruction::SGTZ { rd, rs1 } => {
                    let rs1 = self.x_registers.get(*rs1);
                    let gt = self.executor.gt(rs1, Integer::Public(0))?;
                    debug!("sgtz gt = {gt:?}");
                    self.x_registers.set(*rd, gt);
                }
                Instruction::BEQZ { rs1, label } => {
                    let rs1 = self.x_registers.get(*rs1);
                    let eq = self.executor.beq(rs1, Integer::Public(0))?;
                    if eq {
                        debug!("beqz taking branch");
                        self.pc = program.offset(label, self.pc)?;
                    }
                }
                Instruction::BNEZ { rs1, label } => {
                    let rs1 = self.x_registers.get(*rs1);
                    let eq = self.executor.beq(rs1, Integer::Public(0))?;
                    if !eq {
                        debug!("bnez taking branch");
                        self.pc = program.offset(label, self.pc)?;
                    }
                }
                Instruction::BLEZ { rs1, label } => {
                    let rs1 = self.x_registers.get(*rs1);
                    let le = self.executor.ble(rs1, Integer::Public(0))?;
                    if le {
                        debug!("blez taking branch");
                        self.pc = program.offset(label, self.pc)?;
                    }
                }
                Instruction::BGEZ { rs1, label } => {
                    let rs1 = self.x_registers.get(*rs1);
                    let ge = self.executor.bge(rs1, Integer::Public(0))?;
                    if ge {
                        debug!("bgez taking branch");
                        self.pc = program.offset(label, self.pc)?;
                    }
                }
                Instruction::BLTZ { rs1, label } => {
                    let rs1 = self.x_registers.get(*rs1);
                    let lt = self.executor.blt(rs1, Integer::Public(0))?;
                    if lt {
                        debug!("bltz taking branch");
                        self.pc = program.offset(label, self.pc)?;
                    }
                }
                Instruction::BGTZ { rs1, label } => {
                    let rs1 = self.x_registers.get(*rs1);
                    let gt = self.executor.bgt(rs1, Integer::Public(0))?;
                    if gt {
                        debug!("bgtz taking branch");
                        self.pc = program.offset(label, self.pc)?;
                    }
                }
                Instruction::BGT { rs1, rs2, label } => {
                    let rs1 = self.x_registers.get(*rs1);
                    let rs2 = self.x_registers.get(*rs2);
                    let gt = self.executor.bgt(rs1, rs2)?;
                    if gt {
                        debug!("bgt taking branch");
                        self.pc = program.offset(label, self.pc)?;
                    }
                }
                Instruction::BLE { rs1, rs2, label } => {
                    let rs1 = self.x_registers.get(*rs1);
                    let rs2 = self.x_registers.get(*rs2);
                    let le = self.executor.ble(rs1, rs2)?;
                    if le {
                        debug!("ble taking branch");
                        self.pc = program.offset(label, self.pc)?;
                    }
                }
                Instruction::J { label } => {
                    debug!("jump to {label}");
                    self.pc = program.offset(label, self.pc)?;
                }
                Instruction::JR { rs1 } => {
                    if let Integer::Public(address) = self.x_registers.get(*rs1) {
                        debug!("jump to {address}");
                        self.pc = address;
                    } else {
                        return Err(Error::SecretValueAsAddress);
                    }
                }
                Instruction::RET => {
                    if let Integer::Public(address) = self.x_registers.get(XRegister::x1) {
                        // ignore trailing ret if no calls were made
                        if self.call_depth > 0 {
                            self.pc = address;
                            self.call_depth -= 1;
                        } else {
                            break;
                        }
                    } else {
                        return Err(Error::SecretValueAsAddress);
                    }
                }
                Instruction::CALL { rd, label } => {
                    debug!("call {label}");
                    if label.trim_end_matches("@plt").eq("memcpy") {
                        let dst = self.x_registers.get(XRegister::x10).as_public().unwrap();
                        let src = self.x_registers.get(XRegister::x11).as_public().unwrap();
                        let n = self.x_registers.get(XRegister::x12).as_public().unwrap();
                        debug!("memcpy dst = {dst} src = {src} n = {n}");
                        assert!(n % U64_BYTES == 0);
                        for i in 0..n / U64_BYTES {
                            let val = self.memory.load(src + i * U64_BYTES).unwrap();
                            self.memory.store(dst + i * U64_BYTES, val).unwrap()
                        }
                    } else if label.trim_end_matches("@plt").eq("memset") {
                        let dst = self.x_registers.get(XRegister::x10).as_public().unwrap();
                        let c = self.x_registers.get(XRegister::x11);
                        let n = self.x_registers.get(XRegister::x12).as_public().unwrap();
                        assert!(n % U64_BYTES == 0);
                        for i in 0..n / U64_BYTES {
                            self.memory.store(dst + i * U64_BYTES, c.into()).unwrap()
                        }
                    } else {
                        let address = program.offset(&Label::Text(label.clone()), self.pc)?;
                        // handle call to outlined function
                        if let Some(rd) = rd {
                            self.x_registers.set(*rd, Integer::Public(self.pc));
                        } else {
                            self.x_registers
                                .set(XRegister::x1, Integer::Public(self.pc));
                            self.call_depth += 1;
                        }
                        self.pc = address;
                    }
                }
                Instruction::TAIL { label } => {
                    debug!("tail {label}");
                    // same as call but dont write return address to x1
                    self.pc = program.offset(&Label::Text(label.clone()), self.pc)?;
                    self.call_depth += 1;
                }
                Instruction::Label(_) => {}
                Instruction::FADD { rd, rs1, rs2 } => {
                    let rs1 = self.f_registers.get(*rs1);
                    let rs2 = self.f_registers.get(*rs2);
                    let res = self.executor.fadd(rs1, rs2)?;
                    debug!("fadd res = {res:?}");
                    self.f_registers.set(*rd, res);
                }
                Instruction::FSUB { rd, rs1, rs2 } => {
                    let rs1 = self.f_registers.get(*rs1);
                    let rs2 = self.f_registers.get(*rs2);
                    let res = self.executor.fsub(rs1, rs2)?;
                    debug!("fsub res = {res:?}");
                    self.f_registers.set(*rd, res);
                }
                Instruction::FMUL { rd, rs1, rs2 } => {
                    let rs1 = self.f_registers.get(*rs1);
                    let rs2 = self.f_registers.get(*rs2);
                    let res = self.executor.fmul(rs1, rs2)?;
                    debug!("fmul res = {res:?}");
                    self.f_registers.set(*rd, res);
                }
                Instruction::FDIV { rd, rs1, rs2 } => {
                    let rs1 = self.f_registers.get(*rs1);
                    let rs2 = self.f_registers.get(*rs2);
                    let res = self.executor.fdiv(rs1, rs2)?;
                    debug!("fdiv res = {res:?}");
                    self.f_registers.set(*rd, res);
                }
                Instruction::FMIN { rd, rs1, rs2 } => {
                    let rs1 = self.f_registers.get(*rs1);
                    let rs2 = self.f_registers.get(*rs2);
                    let res = self.executor.fmin(rs1, rs2)?;
                    debug!("fmin res = {res:?}");
                    self.f_registers.set(*rd, res);
                }
                Instruction::FMAX { rd, rs1, rs2 } => {
                    let rs1 = self.f_registers.get(*rs1);
                    let rs2 = self.f_registers.get(*rs2);
                    let res = self.executor.fmax(rs1, rs2)?;
                    debug!("fmax res = {res:?}");
                    self.f_registers.set(*rd, res);
                }
                Instruction::FSQRT { rd, rs1 } => {
                    let rs1 = self.f_registers.get(*rs1);
                    let res = self.executor.fsqrt(rs1)?;
                    debug!("fsqrt res = {res:?}");
                    self.f_registers.set(*rd, res);
                }
                Instruction::FLD { rd, offset, rs1 } => {
                    let base = self
                        .x_registers
                        .get(*rs1)
                        .as_public()
                        .ok_or(Error::SecretValueAsAddress)?;
                    let address = base + *offset as u64;
                    let value = self.memory.load(address)?;
                    self.f_registers.set(*rd, value.try_into()?);
                }
                Instruction::FSD { rs2, offset, rs1 } => {
                    let base = self
                        .x_registers
                        .get(*rs1)
                        .as_public()
                        .ok_or(Error::SecretValueAsAddress)?;
                    let address = base + *offset as u64;
                    let value = self.f_registers.get(*rs2).into();
                    self.memory.store(address, value)?;
                }
                Instruction::FMADD { rd, rs1, rs2, rs3 } => {
                    let rs1 = self.f_registers.get(*rs1);
                    let rs2 = self.f_registers.get(*rs2);
                    let rs3 = self.f_registers.get(*rs3);
                    let res = self.executor.fmul(rs1, rs2)?;
                    let res = self.executor.fadd(res, rs3)?;
                    debug!("fmadd res = {res:?}");
                    self.f_registers.set(*rd, res);
                }
                Instruction::FMSUB { rd, rs1, rs2, rs3 } => {
                    let rs1 = self.f_registers.get(*rs1);
                    let rs2 = self.f_registers.get(*rs2);
                    let rs3 = self.f_registers.get(*rs3);
                    let res = self.executor.fmul(rs1, rs2)?;
                    let res = self.executor.fsub(res, rs3)?;
                    debug!("fmsub res = {res:?}");
                    self.f_registers.set(*rd, res);
                }
                Instruction::FNMADD { rd, rs1, rs2, rs3 } => {
                    let rs1 = self.f_registers.get(*rs1);
                    let rs2 = self.f_registers.get(*rs2);
                    let rs3 = self.f_registers.get(*rs3);
                    let res = self.executor.fmul(rs1, rs2)?;
                    let res = self.executor.fadd(res, rs3)?;
                    let res = self.executor.fneg(res)?;
                    debug!("fnmadd res = {res:?}");
                    self.f_registers.set(*rd, res);
                }
                Instruction::FNMSUB { rd, rs1, rs2, rs3 } => {
                    let rs1 = self.f_registers.get(*rs1);
                    let rs2 = self.f_registers.get(*rs2);
                    let rs3 = self.f_registers.get(*rs3);
                    let res = self.executor.fmul(rs1, rs2)?;
                    let res = self.executor.fsub(res, rs3)?;
                    let res = self.executor.fneg(res)?;
                    debug!("fnmsub res = {res:?}");
                    self.f_registers.set(*rd, res);
                }
                Instruction::FCVTLUD { rd, rs1 } => {
                    let rs1 = self.f_registers.get(*rs1);
                    let res = self.executor.fcvtlud(rs1)?;
                    self.x_registers.set(*rd, res);
                }
                Instruction::FCVTDLU { rd, rs1 } => {
                    let rs1 = self.x_registers.get(*rs1);
                    let res = self.executor.fcvtdlu(rs1)?;
                    self.f_registers.set(*rd, res);
                }
                Instruction::FMV { rd, rs1 } => {
                    let rs1 = self.f_registers.get(*rs1);
                    self.f_registers.set(*rd, rs1);
                }
                Instruction::FMVXD { rd, rs1 } => {
                    let rs1 = self.f_registers.get(*rs1);
                    match rs1 {
                        Float::Public(x) => self.x_registers.set(*rd, Integer::Public(x.to_bits())),
                        Float::Secret(_) => todo!("secret float to integer"),
                    }
                }
                Instruction::FMVDX { rd, rs1 } => {
                    let rs1 = self.x_registers.get(*rs1);
                    match rs1 {
                        Integer::Public(x) => {
                            self.f_registers.set(*rd, Float::Public(f64::from_bits(x)))
                        }
                        Integer::Secret(_) => todo!("secret integer to float"),
                    }
                }
                Instruction::FSGNJ { rd, rs1, rs2 } => {
                    let rs1 = self.f_registers.get(*rs1);
                    let rs2 = self.f_registers.get(*rs2);
                    let res = self.executor.fsgnj(rs1, rs2)?;
                    debug!("fsgnj res = {res:?}");
                    self.f_registers.set(*rd, res);
                }
                Instruction::FSGNJN { rd, rs1, rs2 } => {
                    let rs1 = self.f_registers.get(*rs1);
                    let rs2 = self.f_registers.get(*rs2);
                    let res = self.executor.fsgnjn(rs1, rs2)?;
                    debug!("fsgnjn res = {res:?}");
                    self.f_registers.set(*rd, res);
                }
                Instruction::FSGNJX { rd, rs1, rs2 } => {
                    let rs1 = self.f_registers.get(*rs1);
                    let rs2 = self.f_registers.get(*rs2);
                    let res = self.executor.fsgnjx(rs1, rs2)?;
                    debug!("fsgnjx res = {res:?}");
                    self.f_registers.set(*rd, res);
                }
                Instruction::FEQ { rd, rs1, rs2 } => {
                    let rs1 = self.f_registers.get(*rs1);
                    let rs2 = self.f_registers.get(*rs2);
                    let eq = self.executor.feq(rs1, rs2)?;
                    debug!("feq = {eq:?}");
                    self.x_registers.set(*rd, eq);
                }
                Instruction::FLT { rd, rs1, rs2 } => {
                    let rs1 = self.f_registers.get(*rs1);
                    let rs2 = self.f_registers.get(*rs2);
                    let lt = self.executor.flt(rs1, rs2)?;
                    debug!("flt = {lt:?}");
                    self.x_registers.set(*rd, lt);
                }
                Instruction::FLE { rd, rs1, rs2 } => {
                    let rs1 = self.f_registers.get(*rs1);
                    let rs2 = self.f_registers.get(*rs2);
                    let le = self.executor.fle(rs1, rs2)?;
                    debug!("fle = {le:?}");
                    self.x_registers.set(*rd, le);
                }
                Instruction::FCLASS { rd, rs1 } => {
                    let rs1 = self.f_registers.get(*rs1);
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
                    self.x_registers.set(*rd, Integer::Public(class));
                }
                Instruction::FNEG { rd, rs1 } => {
                    let rs1 = self.f_registers.get(*rs1);
                    let res = self.executor.fneg(rs1)?;
                    debug!("fneg res = {res:?}");
                    self.f_registers.set(*rd, res);
                }
                Instruction::FABS { rd, rs1 } => {
                    let rs1 = self.f_registers.get(*rs1);
                    let res = self.executor.fabs(rs1)?;
                    debug!("fabs res = {res:?}");
                    self.f_registers.set(*rd, res);
                }
                Instruction::VSETVL { rd, rs1, rs2: _ } => {
                    self.x_registers
                        .set(*rd, Integer::Public(self.v_registers.vl));
                    self.v_registers.vl = self
                        .x_registers
                        .get(*rs1)
                        .as_public()
                        .ok_or(Error::UnexpectedValue)?;
                }
                Instruction::VSETVLI { rd, rs1, imm: _ } => {
                    self.x_registers
                        .set(*rd, Integer::Public(self.v_registers.vl));
                    self.v_registers.vl = self
                        .x_registers
                        .get(*rs1)
                        .as_public()
                        .ok_or(Error::UnexpectedValue)?;
                }
                Instruction::VLE { vd, rs1 } => {
                    let address = self
                        .x_registers
                        .get(*rs1)
                        .as_public()
                        .ok_or(Error::SecretValueAsAddress)?;
                    let res = (0..self.v_registers.vl)
                        .map(|i| self.memory.load(address + i * U64_BYTES))
                        .collect::<Result<Vec<Value>>>()?;
                    self.v_registers.set(*vd, res);
                }
                Instruction::VSE { vs2, rs1 } => {
                    let address = self
                        .x_registers
                        .get(*rs1)
                        .as_public()
                        .ok_or(Error::SecretValueAsAddress)?;
                    let vs2 = self.v_registers.get(*vs2);
                    for (i, value) in vs2.iter().enumerate() {
                        self.memory.store(address + i as u64 * U64_BYTES, *value)?;
                    }
                }
                Instruction::VMULVV { vd, vs1, vs2 } => {
                    let vs1 = self
                        .v_registers
                        .get(*vs1)
                        .iter()
                        .copied()
                        .map(TryInto::try_into)
                        .collect::<Result<Vec<Integer>>>()?;
                    let vs2 = self
                        .v_registers
                        .get(*vs2)
                        .iter()
                        .copied()
                        .map(TryInto::try_into)
                        .collect::<Result<Vec<Integer>>>()?;
                    let res = self
                        .executor
                        .vmul(&vs1, &vs2)?
                        .into_iter()
                        .map(Into::into)
                        .collect();
                    debug!("vmulvv res = {res:?}");
                    self.v_registers.set(*vd, res);
                }
                Instruction::VMULVX { vd, rs1, vs2 } => {
                    let rs1 = self.x_registers.get(*rs1);
                    let vs1 = vec![rs1; self.v_registers.vl as usize];
                    let vs2 = self
                        .v_registers
                        .get(*vs2)
                        .iter()
                        .copied()
                        .map(TryInto::try_into)
                        .collect::<Result<Vec<Integer>>>()?;
                    let res = self
                        .executor
                        .vmul(&vs1, &vs2)?
                        .into_iter()
                        .map(Into::into)
                        .collect();
                    debug!("vmulvx res = {res:?}");
                    self.v_registers.set(*vd, res);
                }
                Instruction::VFMULVV { vd, vs1, vs2 } => {
                    let vs1 = self
                        .v_registers
                        .get(*vs1)
                        .iter()
                        .copied()
                        .map(TryInto::try_into)
                        .collect::<Result<Vec<Float>>>()?;
                    let vs2 = self
                        .v_registers
                        .get(*vs2)
                        .iter()
                        .copied()
                        .map(TryInto::try_into)
                        .collect::<Result<Vec<Float>>>()?;
                    let res = self
                        .executor
                        .vfmul(&vs1, &vs2)?
                        .into_iter()
                        .map(Into::into)
                        .collect();
                    debug!("vfmulvv res = {res:?}");
                    self.v_registers.set(*vd, res);
                }
                Instruction::VFMULVF { vd, rs1, vs2 } => {
                    let rs1 = self.f_registers.get(*rs1);
                    let vs1 = vec![rs1; self.v_registers.vl as usize];
                    let vs2 = self
                        .v_registers
                        .get(*vs2)
                        .iter()
                        .copied()
                        .map(TryInto::try_into)
                        .collect::<Result<Vec<Float>>>()?;
                    let res = self
                        .executor
                        .vfmul(&vs1, &vs2)?
                        .into_iter()
                        .map(Into::into)
                        .collect();
                    debug!("vfmulvf res = {res:?}");
                    self.v_registers.set(*vd, res);
                }
                Instruction::VANDVV { vd, vs1, vs2 } => {
                    let vs1 = self
                        .v_registers
                        .get(*vs1)
                        .iter()
                        .copied()
                        .map(TryInto::try_into)
                        .collect::<Result<Vec<Integer>>>()?;
                    let vs2 = self
                        .v_registers
                        .get(*vs2)
                        .iter()
                        .copied()
                        .map(TryInto::try_into)
                        .collect::<Result<Vec<Integer>>>()?;
                    let res = self
                        .executor
                        .vand(&vs1, &vs2)?
                        .into_iter()
                        .map(Into::into)
                        .collect();
                    debug!("vandvv res = {res:?}");
                    self.v_registers.set(*vd, res);
                }
                Instruction::VANDVX { vd, rs1, vs2 } => {
                    let rs1 = self.x_registers.get(*rs1);
                    let vs1 = vec![rs1; self.v_registers.vl as usize];
                    let vs2 = self
                        .v_registers
                        .get(*vs2)
                        .iter()
                        .copied()
                        .map(TryInto::try_into)
                        .collect::<Result<Vec<Integer>>>()?;
                    let res = self
                        .executor
                        .vand(&vs1, &vs2)?
                        .into_iter()
                        .map(Into::into)
                        .collect();
                    debug!("vandvx res = {res:?}");
                    self.v_registers.set(*vd, res);
                }
                Instruction::VANDVI { vd, imm, vs2 } => {
                    let vs1 = vec![Integer::Public(*imm as u64); self.v_registers.vl as usize];
                    let vs2 = self
                        .v_registers
                        .get(*vs2)
                        .iter()
                        .copied()
                        .map(TryInto::try_into)
                        .collect::<Result<Vec<Integer>>>()?;
                    let res = self
                        .executor
                        .vand(&vs1, &vs2)?
                        .into_iter()
                        .map(Into::into)
                        .collect();
                    debug!("vandvi res = {res:?}");
                    self.v_registers.set(*vd, res);
                }
                Instruction::DWORD(_) => {}
            };
            self.pc += 1;
        }
        let duration = start.elapsed();
        info!("execution done, took {}ms", duration.as_millis());
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::{PartyBuilder, PARTY_0};
    use crate::{
        channel::{Message, ThreadChannel},
        mpc_executor::EmbedFixedPoint,
        party::PARTY_1,
        registers::XRegister,
        types::Integer,
        Float, Program, Result, Share, U64_BYTES,
    };
    use std::{
        collections::BTreeSet,
        fs::File,
        io::{self, BufReader, Read},
        sync::mpsc::{self, Receiver, Sender},
        thread,
        time::Instant,
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
                .register_u64(XRegister::x10, Integer::Public(5))
                .build()?;
            party.execute(&program.parse()?)?;
            party.register_u64(XRegister::x10)
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
                .register_u64(XRegister::x10, Integer::Public(10))
                .build()?;
            party.execute(&program.parse()?)?;
            party.register_u64(XRegister::x10)
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
                .register_u64(XRegister::x10, Integer::Public(set0_address))
                .register_u64(XRegister::x11, Integer::Public(set0_len))
                .register_u64(XRegister::x12, Integer::Public(set1_address))
                .register_u64(XRegister::x13, Integer::Public(set1_len))
                .register_u64(XRegister::x14, Integer::Public(intersection_addr))
                .address_range_u64(
                    set_address,
                    set.iter()
                        .map(|x| Integer::Secret(Share::Arithmetic(*x)))
                        .collect(),
                )?
                .build()?;

            party.execute(&program.parse()?)?;

            let len = party.register_u64(XRegister::x10)?;

            party.address_range_u64(intersection_addr..intersection_addr + U64_BYTES * len)
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
            sum:
                    li      a2, 0
                    beq     a0, a1, .LBB1_3
                    sub     a1, a1, a0
                    srli    a1, a1, 3
            .LBB1_2:
                    ld      a3, 0(a0)
                    add     a2, a2, a3
                    addi    a1, a1, -1
                    addi    a0, a0, 8
                    bnez    a1, .LBB1_2
            .LBB1_3:
                    mv      a0, a2
                    ret

            mean:
                    addi    sp, sp, -48
                    sd      ra, 40(sp)
                    sd      s0, 32(sp)
                    sd      s1, 24(sp)
                    sd      s2, 16(sp)
                    sd      s3, 8(sp)
                    mv      s3, a3
                    mv      s0, a2
                    mv      s1, a1
                    slli    a1, a1, 3
                    add     a1, a1, a0
                    call    sum
                    mv      s2, a0
                    slli    a1, s3, 3
                    add     a1, a1, s0
                    mv      a0, s0
                    call    sum
                    add     s1, s1, s3
                    beqz    s1, .LBB4_2
                    add     a0, a0, s2
                    divu    a0, a0, s1
                    ld      ra, 40(sp)
                    ld      s0, 32(sp)
                    ld      s1, 24(sp)
                    ld      s2, 16(sp)
                    ld      s3, 8(sp)
                    addi    sp, sp, 48
                    ret
            .LBB4_2:
        ";

        let (ch0, ch1) = create_channels();

        let salaries0 = [1000, 2500, 1900, 3000, 2750, 5000];
        let salaries1 = [1200, 3500, 900, 4000, 1750, 1000];
        let sal0_len = salaries0.len() as u64;
        let sal1_len = salaries1.len() as u64;
        let mean = salaries0.iter().chain(salaries1.iter()).sum::<u64>() / (sal0_len + sal1_len);

        let base_addr = 0x0;
        let sal0_addr = base_addr;
        let sal1_addr = base_addr + U64_BYTES * sal0_len;

        let run = move |id: usize,
                        ch: ThreadChannel,
                        salaries: &[u64],
                        salaries_address: u64|
              -> Result<u64> {
            let mut party = PartyBuilder::new(id, ch)
                .register_u64(XRegister::x10, Integer::Public(sal0_addr))
                .register_u64(XRegister::x11, Integer::Public(sal0_len))
                .register_u64(XRegister::x12, Integer::Public(sal1_addr))
                .register_u64(XRegister::x13, Integer::Public(sal1_len))
                .address_range_u64(
                    salaries_address,
                    salaries
                        .iter()
                        .map(|x| Integer::Secret(Share::Arithmetic(*x)))
                        .collect(),
                )?
                .build()?;

            party.execute(&program.parse::<Program>()?.with_entry("mean")?)?;

            party.register_u64(XRegister::x10)
        };

        let party0 = thread::spawn(move || run(PARTY_0, ch0, &salaries0, sal0_addr));
        let party1 = thread::spawn(move || run(PARTY_1, ch1, &salaries1, sal1_addr));

        let mean0 = party0.join().unwrap().unwrap();
        let mean1 = party1.join().unwrap().unwrap();

        assert!(mean0.abs_diff(mean) <= 1);
        assert!(mean1.abs_diff(mean) <= 1);

        Ok(())
    }

    #[test]
    fn vec_mul() -> Result<()> {
        let program = "
            vsetvli  x0,a3,e64
            vle.v    v0,a0
            vle.v    v1,a1
            vmul.vv  v0,v0,v1
            vse.v    v0,a2
        ";

        let n = 100;

        let (ch0, ch1) = create_channels();
        let run = move |id: usize,
                        ch: ThreadChannel,
                        vec: &[u64],
                        vec_address: u64|
              -> Result<Vec<u64>> {
            let mut party = PartyBuilder::new(id, ch)
                .register_u64(XRegister::x10, Integer::Public(0x0))
                .register_u64(XRegister::x11, Integer::Public(U64_BYTES * n))
                .register_u64(XRegister::x12, Integer::Public(U64_BYTES * 2 * n))
                .register_u64(XRegister::x13, Integer::Public(n))
                .address_range_u64(
                    vec_address,
                    vec.iter()
                        .map(|x| Integer::Secret(Share::Arithmetic(*x)))
                        .collect(),
                )?
                .build()?;
            let start = Instant::now();
            party.execute(&program.parse()?)?;
            println!("vmul took {}ms", start.elapsed().as_millis());
            party.address_range_u64(U64_BYTES * 2 * n..U64_BYTES * 3 * n)
        };
        let vec0 = (0..n).map(|_| rand::random()).collect::<Vec<u64>>();
        let vec1 = (0..n).map(|_| rand::random()).collect::<Vec<u64>>();
        let res = vec0
            .iter()
            .zip(vec1.iter())
            .map(|(a, b)| a.wrapping_mul(*b))
            .collect::<Vec<u64>>();
        let party0 = thread::spawn(move || run(PARTY_0, ch0, &vec0, 0));
        let party1 = thread::spawn(move || run(PARTY_1, ch1, &vec1, U64_BYTES * n));

        let res0 = party0.join().unwrap().unwrap();
        let res1 = party1.join().unwrap().unwrap();

        assert_eq!(res0, res);
        assert_eq!(res1, res);

        Ok(())
    }

    #[test]
    fn mul() -> Result<()> {
        // https://godbolt.org/z/6P3eM3WW9
        let program = "
            mul:
                    li      a6, 0
                    beqz    a1, .LBB1_2
            .LBB1_1:
                    ld      a5, 0(a0)
                    ld      a3, 0(a2)
                    addi    a6, a6, 1
                    mul     a3, a3, a5
                    sd      a3, 0(a4)
                    addi    a0, a0, 8
                    addi    a2, a2, 8
                    addi    a4, a4, 8
                    bne     a1, a6, .LBB1_1
            .LBB1_2:
                    ret
        ";

        let n = 100;

        let (ch0, ch1) = create_channels();
        let run = move |id: usize,
                        ch: ThreadChannel,
                        vec: &[u64],
                        vec_address: u64|
              -> Result<Vec<u64>> {
            let mut party = PartyBuilder::new(id, ch)
                .register_u64(XRegister::x10, Integer::Public(0x0))
                .register_u64(XRegister::x11, Integer::Public(n))
                .register_u64(XRegister::x12, Integer::Public(U64_BYTES * n))
                .register_u64(XRegister::x13, Integer::Public(n))
                .register_u64(XRegister::x14, Integer::Public(U64_BYTES * 2 * n))
                .address_range_u64(
                    vec_address,
                    vec.iter()
                        .map(|x| Integer::Secret(Share::Arithmetic(*x)))
                        .collect(),
                )?
                .build()?;
            let start = Instant::now();
            party.execute(&program.parse()?)?;
            println!("mul took {}ms", start.elapsed().as_millis());
            party.address_range_u64(U64_BYTES * 2 * n..U64_BYTES * 3 * n)
        };
        let vec0 = (0..n).map(|_| rand::random()).collect::<Vec<u64>>();
        let vec1 = (0..n).map(|_| rand::random()).collect::<Vec<u64>>();
        let res = vec0
            .iter()
            .zip(vec1.iter())
            .map(|(a, b)| a.wrapping_mul(*b))
            .collect::<Vec<u64>>();
        let party0 = thread::spawn(move || run(PARTY_0, ch0, &vec0, 0));
        let party1 = thread::spawn(move || run(PARTY_1, ch1, &vec1, U64_BYTES * n));

        let res0 = party0.join().unwrap().unwrap();
        let res1 = party1.join().unwrap().unwrap();

        assert_eq!(res0, res);
        assert_eq!(res1, res);

        Ok(())
    }

    #[test]
    fn ascon_round() -> Result<()> {
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

        let party0 = thread::spawn(move || {
            let mut party = PartyBuilder::new(PARTY_0, ch0)
                .register_u64(XRegister::x10, Integer::Public(0x0))
                .register_u64(XRegister::x11, Integer::Public(U64_BYTES * 5))
                .register_u64(XRegister::x12, Integer::Public(0x1f))
                .address_range_u64(
                    U64_BYTES * 5,
                    vec![
                        Integer::Secret(Share::Binary(0x0123456789abcdef)),
                        Integer::Secret(Share::Binary(0x23456789abcdef01)),
                        Integer::Secret(Share::Binary(0x456789abcdef0123)),
                        Integer::Secret(Share::Binary(0x6789abcdef012345)),
                        Integer::Secret(Share::Binary(0x89abcde01234567f)),
                    ],
                )?
                .build()?;
            party.execute(&program.parse()?)?;
            party.address_range_u64(0x0..U64_BYTES * 5)
        });
        let party1 = thread::spawn(move || {
            let mut party = PartyBuilder::new(PARTY_1, ch1)
                .register_u64(XRegister::x10, Integer::Public(0x0))
                .register_u64(XRegister::x11, Integer::Public(U64_BYTES * 5))
                .register_u64(XRegister::x12, Integer::Public(0x1f))
                .build()?;
            party.execute(&program.parse()?)?;
            party.address_range_u64(0x0..U64_BYTES * 5)
        });

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

    fn u64_arr_to_be_bytes(x: &[u64]) -> Vec<u8> {
        x.iter()
            .flat_map(|x| u64::to_be_bytes(*x))
            .collect::<Vec<u8>>()
    }

    fn u64_arr_from_be_bytes(x: &[u8]) -> Vec<u64> {
        x.chunks_exact(8)
            .map(|x| u64::from_be_bytes(x.try_into().unwrap()))
            .collect::<Vec<u64>>()
    }

    #[test]
    fn ascon_hash() -> Result<()> {
        // https://godbolt.org/z/v7Gj7KjhG
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

            permute_12:
                    addi    sp, sp, -96
                    sd      ra, 88(sp)
                    sd      s0, 80(sp)
                    mv      s0, a0
                    addi    a0, sp, 40
                    li      a2, 240
                    mv      a1, s0
                    call    round@plt
                    mv      a0, sp
                    addi    a1, sp, 40
                    li      a2, 225
                    call    round@plt
                    addi    a0, sp, 40
                    mv      a1, sp
                    li      a2, 210
                    call    round@plt
                    mv      a0, sp
                    addi    a1, sp, 40
                    li      a2, 195
                    call    round@plt
                    addi    a0, sp, 40
                    mv      a1, sp
                    li      a2, 180
                    call    round@plt
                    mv      a0, sp
                    addi    a1, sp, 40
                    li      a2, 165
                    call    round@plt
                    addi    a0, sp, 40
                    mv      a1, sp
                    li      a2, 150
                    call    round@plt
                    mv      a0, sp
                    addi    a1, sp, 40
                    li      a2, 135
                    call    round@plt
                    addi    a0, sp, 40
                    mv      a1, sp
                    li      a2, 120
                    call    round@plt
                    mv      a0, sp
                    addi    a1, sp, 40
                    li      a2, 105
                    call    round@plt
                    addi    a0, sp, 40
                    mv      a1, sp
                    li      a2, 90
                    call    round@plt
                    addi    a1, sp, 40
                    li      a2, 75
                    mv      a0, s0
                    call    round@plt
                    ld      ra, 88(sp)
                    ld      s0, 80(sp)
                    addi    sp, sp, 96
                    ret

            .LCPI2_0:
                    .quad   -1255492011513352131
            .LCPI2_1:
                    .quad   -8380609354527731710
            .LCPI2_2:
                    .quad   -5437372128236807582
            .LCPI2_3:
                    .quad   4834782570098516968
            .LCPI2_4:
                    .quad   3787428097924915520
            ascon_hash:
                    addi    sp, sp, -80
                    sd      ra, 72(sp)
                    sd      s0, 64(sp)
                    sd      s1, 56(sp)
                    sd      s2, 48(sp)
            .Lpcrel_hi0:
                    auipc   a3, %pcrel_hi(.LCPI2_0)
                    ld      a3, %pcrel_lo(.Lpcrel_hi0)(a3)
                    mv      s2, a2
                    sd      a3, 8(sp)
            .Lpcrel_hi1:
                    auipc   a2, %pcrel_hi(.LCPI2_1)
                    ld      a2, %pcrel_lo(.Lpcrel_hi1)(a2)
            .Lpcrel_hi2:
                    auipc   a3, %pcrel_hi(.LCPI2_2)
                    ld      a3, %pcrel_lo(.Lpcrel_hi2)(a3)
            .Lpcrel_hi3:
                    auipc   a4, %pcrel_hi(.LCPI2_3)
                    ld      a4, %pcrel_lo(.Lpcrel_hi3)(a4)
            .Lpcrel_hi4:
                    auipc   a5, %pcrel_hi(.LCPI2_4)
                    ld      a5, %pcrel_lo(.Lpcrel_hi4)(a5)
                    sd      a2, 16(sp)
                    sd      a3, 24(sp)
                    sd      a4, 32(sp)
                    sd      a5, 40(sp)
                    slli    s1, a1, 3
                    beqz    s1, .LBB2_2
            .LBB2_1:
                    ld      a1, 0(a0)
                    ld      a2, 8(sp)
                    addi    s0, a0, 8
                    xor     a1, a1, a2
                    sd      a1, 8(sp)
                    addi    a0, sp, 8
                    call    permute_12@plt
                    addi    s1, s1, -8
                    mv      a0, s0
                    bnez    s1, .LBB2_1
            .LBB2_2:
                    ld      a0, 8(sp)
                    mv      s0, s2
                    sd      a0, 0(s0)
                    addi    a0, sp, 8
                    call    permute_12@plt
                    ld      a0, 8(sp)
                    sd      a0, 8(s0)
                    addi    a0, sp, 8
                    call    permute_12@plt
                    ld      a0, 8(sp)
                    sd      a0, 16(s0)
                    addi    a0, sp, 8
                    call    permute_12@plt
                    ld      a0, 8(sp)
                    sd      a0, 24(s0)
                    ld      ra, 72(sp)
                    ld      s0, 64(sp)
                    ld      s1, 56(sp)
                    ld      s2, 48(sp)
                    addi    sp, sp, 80
                    ret
        ";

        let input0 = b"\x00\x01\x02\x03\x04\x05\x06\x07";
        let input1 = b"\x80\x00\x00\x00\x00\x00\x00\x00";
        let in0_len = input0.len() as u64 / 8;
        let in1_len = input1.len() as u64 / 8;

        let in0_addr = 0x0;
        let in1_addr = in0_addr + U64_BYTES * in0_len;
        let out_addr = in1_addr + U64_BYTES * in1_len;

        let (ch0, ch1) = create_channels();
        let run = move |id: usize,
                        ch: ThreadChannel,
                        inputs: &[u8],
                        inputs_addr: u64|
              -> Result<Vec<u8>> {
            let mut party = PartyBuilder::new(id, ch)
                .register_u64(XRegister::x10, Integer::Public(in0_addr))
                .register_u64(XRegister::x11, Integer::Public(in0_len + in1_len))
                .register_u64(XRegister::x12, Integer::Public(out_addr))
                .address_range_u64(
                    inputs_addr,
                    u64_arr_from_be_bytes(inputs)
                        .iter()
                        .map(|x| Integer::Secret(Share::Binary(*x)))
                        .collect(),
                )?
                // .n_and_triples(15 * 12 * (3 + in0_len + in1_len))
                .build()?;
            party.execute(&program.parse::<Program>()?.with_entry("ascon_hash")?)?;
            Ok(u64_arr_to_be_bytes(
                &party.address_range_u64(out_addr..out_addr + U64_BYTES * 4)?,
            ))
        };

        let party0 = thread::spawn(move || run(PARTY_0, ch0, input0, in0_addr));
        let party1 = thread::spawn(move || run(PARTY_1, ch1, input1, in1_addr));

        let res0 = party0.join().unwrap().unwrap();
        let res1 = party1.join().unwrap().unwrap();

        let expected = b"\xf4\xc6\xa4\x4b\x29\x91\x5d\x3d\x57\xcf\x92\x8a\x18\xec\x62\x26\xbb\x8d\xd6\xc1\x13\x6a\xcd\x24\x96\x5f\x7e\x77\x80\xcd\x69\xcf";

        assert_eq!(res0, expected);
        assert_eq!(res1, expected);

        Ok(())
    }

    #[test]
    fn ascon_aead() -> Result<()> {
        // https://godbolt.org/z/oE9WEMfPv
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

            permute_12:
                    addi    sp, sp, -96
                    sd      ra, 88(sp)
                    sd      s0, 80(sp)
                    mv      s0, a0
                    addi    a0, sp, 40
                    li      a2, 240
                    mv      a1, s0
                    call    round@plt
                    mv      a0, sp
                    addi    a1, sp, 40
                    li      a2, 225
                    call    round@plt
                    addi    a0, sp, 40
                    mv      a1, sp
                    li      a2, 210
                    call    round@plt
                    mv      a0, sp
                    addi    a1, sp, 40
                    li      a2, 195
                    call    round@plt
                    addi    a0, sp, 40
                    mv      a1, sp
                    li      a2, 180
                    call    round@plt
                    mv      a0, sp
                    addi    a1, sp, 40
                    li      a2, 165
                    call    round@plt
                    addi    a0, sp, 40
                    mv      a1, sp
                    li      a2, 150
                    call    round@plt
                    mv      a0, sp
                    addi    a1, sp, 40
                    li      a2, 135
                    call    round@plt
                    addi    a0, sp, 40
                    mv      a1, sp
                    li      a2, 120
                    call    round@plt
                    mv      a0, sp
                    addi    a1, sp, 40
                    li      a2, 105
                    call    round@plt
                    addi    a0, sp, 40
                    mv      a1, sp
                    li      a2, 90
                    call    round@plt
                    addi    a1, sp, 40
                    li      a2, 75
                    mv      a0, s0
                    call    round@plt
                    ld      ra, 88(sp)
                    ld      s0, 80(sp)
                    addi    sp, sp, 96
                    ret

            permute_6:
                    addi    sp, sp, -96
                    sd      ra, 88(sp)
                    sd      s0, 80(sp)
                    mv      s0, a0
                    addi    a0, sp, 40
                    li      a2, 150
                    mv      a1, s0
                    call    round@plt
                    mv      a0, sp
                    addi    a1, sp, 40
                    li      a2, 135
                    call    round@plt
                    addi    a0, sp, 40
                    mv      a1, sp
                    li      a2, 120
                    call    round@plt
                    mv      a0, sp
                    addi    a1, sp, 40
                    li      a2, 105
                    call    round@plt
                    addi    a0, sp, 40
                    mv      a1, sp
                    li      a2, 90
                    call    round@plt
                    addi    a1, sp, 40
                    li      a2, 75
                    mv      a0, s0
                    call    round@plt
                    ld      ra, 88(sp)
                    ld      s0, 80(sp)
                    addi    sp, sp, 96
                    ret

            process_associated_data:
                    addi    sp, sp, -32
                    sd      ra, 24(sp)
                    sd      s0, 16(sp)
                    sd      s1, 8(sp)
                    sd      s2, 0(sp)
                    mv      s2, a0
                    beqz    a2, .LBB4_4
                    slli    s1, a2, 3
                    beqz    s1, .LBB4_3
            .LBB4_2:
                    ld      a0, 0(a1)
                    mv      a3, s2
                    ld      a2, 0(a3)
                    addi    s0, a1, 8
                    xor     a0, a0, a2
                    sd      a0, 0(a3)
                    mv      a0, s2
                    call    permute_6@plt
                    addi    s1, s1, -8
                    mv      a1, s0
                    bnez    s1, .LBB4_2
            .LBB4_3:
                    mv      a2, s2
                    ld      a0, 0(a2)
                    li      a1, -1
                    slli    a1, a1, 63
                    xor     a0, a0, a1
                    sd      a0, 0(a2)
                    mv      a0, s2
                    call    permute_6@plt
            .LBB4_4:
                    mv      a1, s2
                    ld      a0, 32(a1)
                    xori    a0, a0, 1
                    sd      a0, 32(a1)
                    ld      ra, 24(sp)
                    ld      s0, 16(sp)
                    ld      s1, 8(sp)
                    ld      s2, 0(sp)
                    addi    sp, sp, 32
                    ret

            process_encrypt_inplace:
                    addi    sp, sp, -32
                    sd      ra, 24(sp)
                    sd      s0, 16(sp)
                    sd      s1, 8(sp)
                    sd      s2, 0(sp)
                    mv      s2, a0
                    slli    s1, a2, 3
                    beqz    s1, .LBB5_2
            .LBB5_1:
                    ld      a0, 0(a1)
                    mv      a3, s2
                    ld      a2, 0(a3)
                    addi    s0, a1, 8
                    xor     a0, a0, a2
                    sd      a0, 0(a3)
                    sd      a0, 0(a1)
                    mv      a0, s2
                    call    permute_6@plt
                    addi    s1, s1, -8
                    mv      a1, s0
                    bnez    s1, .LBB5_1
            .LBB5_2:
                    call    t0, OUTLINED_FUNCTION_0
                    ret

            process_decrypt_inplace:
                    addi    sp, sp, -32
                    sd      ra, 24(sp)
                    sd      s0, 16(sp)
                    sd      s1, 8(sp)
                    sd      s2, 0(sp)
                    mv      s2, a0
                    slli    s1, a2, 3
                    beqz    s1, .LBB6_2
            .LBB6_1:
                    ld      a0, 0(a1)
                    mv      a3, s2
                    ld      a2, 0(a3)
                    addi    s0, a1, 8
                    xor     a2, a2, a0
                    sd      a2, 0(a1)
                    sd      a0, 0(a3)
                    mv      a0, s2
                    call    permute_6@plt
                    addi    s1, s1, -8
                    mv      a1, s0
                    bnez    s1, .LBB6_1
            .LBB6_2:
                    call    t0, OUTLINED_FUNCTION_0
                    ret

            process_final:
                    addi    sp, sp, -48
                    sd      ra, 40(sp)
                    sd      s0, 32(sp)
                    sd      s1, 24(sp)
                    sd      s2, 16(sp)
                    sd      s3, 8(sp)
                    mv      s0, a1
                    ld      s2, 0(a2)
                    ld      a1, 8(a1)
                    ld      s1, 8(a2)
                    ld      a2, 16(s0)
                    mv      s3, a0
                    xor     a0, a1, s2
                    sd      a0, 8(s0)
                    xor     a2, a2, s1
                    sd      a2, 16(s0)
                    mv      a0, s0
                    call    permute_12@plt
                    ld      a0, 24(s0)
                    ld      a1, 32(s0)
                    xor     a0, a0, s2
                    sd      a0, 24(s0)
                    xor     a1, a1, s1
                    sd      a1, 32(s0)
                    mv      a2, s3
                    sd      a0, 0(a2)
                    sd      a1, 8(a2)
                    ld      ra, 40(sp)
                    ld      s0, 32(sp)
                    ld      s1, 24(sp)
                    ld      s2, 16(sp)
                    ld      s3, 8(sp)
                    addi    sp, sp, 48
                    ret

            encrypt_inplace:
                    addi    sp, sp, -112
                    sd      ra, 104(sp)
                    sd      s0, 96(sp)
                    sd      s1, 88(sp)
                    sd      s2, 80(sp)
                    sd      s3, 72(sp)
                    sd      s4, 64(sp)
                    sd      s5, 56(sp)
                    sd      s6, 48(sp)
                    sd      s7, 40(sp)
                    mv      s4, a6
                    mv      s6, a5
                    mv      s2, a4
                    mv      s3, a3
                    mv      s7, a1
                    mv      s5, a0
                    ld      s1, 0(a1)
                    ld      s0, 8(a1)
                    ld      a0, 0(a2)
                    ld      a1, 8(a2)
                    lui     a2, 786944
                    addiw   a2, a2, 1539
                    slli    a2, a2, 33
                    sd      a2, 0(sp)
                    sd      s1, 8(sp)
                    sd      s0, 16(sp)
                    sd      a0, 24(sp)
                    sd      a1, 32(sp)
                    mv      a0, sp
                    call    permute_12@plt
                    ld      a0, 24(sp)
                    xor     a0, a0, s1
                    sd      a0, 24(sp)
                    ld      a0, 32(sp)
                    xor     a0, a0, s0
                    sd      a0, 32(sp)
                    mv      a0, sp
                    mv      a1, s6
                    mv      a2, s4
                    call    process_associated_data@plt
                    mv      a0, sp
                    mv      a1, s3
                    mv      a2, s2
                    call    process_encrypt_inplace@plt
                    mv      a1, sp
                    mv      a0, s5
                    mv      a2, s7
                    call    process_final@plt
                    ld      ra, 104(sp)
                    ld      s0, 96(sp)
                    ld      s1, 88(sp)
                    ld      s2, 80(sp)
                    ld      s3, 72(sp)
                    ld      s4, 64(sp)
                    ld      s5, 56(sp)
                    ld      s6, 48(sp)
                    ld      s7, 40(sp)
                    addi    sp, sp, 112
                    ret

            decrypt_inplace:
                    addi    sp, sp, -144
                    sd      ra, 136(sp)
                    sd      s0, 128(sp)
                    sd      s1, 120(sp)
                    sd      s2, 112(sp)
                    sd      s3, 104(sp)
                    sd      s4, 96(sp)
                    sd      s5, 88(sp)
                    sd      s6, 80(sp)
                    sd      s7, 72(sp)
                    mv      s6, a6
                    mv      s2, a5
                    mv      s5, a4
                    mv      s3, a3
                    mv      s4, a2
                    mv      s7, a0
                    ld      s0, 0(a0)
                    ld      s1, 8(a0)
                    ld      a0, 0(a1)
                    ld      a1, 8(a1)
                    lui     a2, 786944
                    addiw   a2, a2, 1539
                    slli    a2, a2, 33
                    sd      a2, 8(sp)
                    sd      s0, 16(sp)
                    sd      s1, 24(sp)
                    sd      a0, 32(sp)
                    sd      a1, 40(sp)
                    addi    a0, sp, 8
                    call    permute_12@plt
                    ld      a0, 32(sp)
                    xor     a0, a0, s0
                    sd      a0, 32(sp)
                    ld      a0, 40(sp)
                    xor     a0, a0, s1
                    sd      a0, 40(sp)
                    addi    a0, sp, 8
                    mv      a1, s5
                    mv      a2, s2
                    call    process_associated_data@plt
                    addi    a0, sp, 8
                    mv      a1, s4
                    mv      a2, s3
                    call    process_decrypt_inplace@plt
                    addi    a0, sp, 48
                    addi    a1, sp, 8
                    mv      a2, s7
                    call    process_final@plt
                    mv      a2, s6
                    ld      a0, 0(a2)
                    ld      a1, 8(a2)
                    ld      a2, 56(sp)
                    ld      a3, 48(sp)
                    xor     a1, a1, a2
                    xor     a0, a0, a3
                    or      a0, a0, a1
                    seqz    a0, a0
                    ld      ra, 136(sp)
                    ld      s0, 128(sp)
                    ld      s1, 120(sp)
                    ld      s2, 112(sp)
                    ld      s3, 104(sp)
                    ld      s4, 96(sp)
                    ld      s5, 88(sp)
                    ld      s6, 80(sp)
                    ld      s7, 72(sp)
                    addi    sp, sp, 144
                    ret

            OUTLINED_FUNCTION_0:
                    mv      a2, s2
                    ld      a0, 0(a2)
                    li      a1, -1
                    slli    a1, a1, 63
                    xor     a0, a0, a1
                    sd      a0, 0(a2)
                    ld      ra, 24(sp)
                    ld      s0, 16(sp)
                    ld      s1, 8(sp)
                    ld      s2, 0(sp)
                    addi    sp, sp, 32
                    jr      t0
        ";

        let pt = u64_arr_from_be_bytes(
            b"\x00\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0a\x0b\x0c\x0d\x0e\x0f",
        );
        let key = u64_arr_from_be_bytes(
            b"\x00\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0a\x0b\x0c\x0d\x0e\x0f",
        );
        let nonce = u64_arr_from_be_bytes(
            b"\x00\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0a\x0b\x0c\x0d\x0e\x0f",
        );

        let key_len = key.len() as u64;
        let nonce_len = nonce.len() as u64;
        let pt_len = pt.len() as u64;
        let ad_len = 0;

        let key_addr = 0x0;
        let nonce_addr = key_addr + key_len * U64_BYTES;
        let pt_addr = nonce_addr + nonce_len * U64_BYTES;
        let ad_addr = pt_addr + pt_len * U64_BYTES;

        let (ch0, ch1) = create_channels();

        let party0 = thread::spawn(move || -> Result<Vec<u64>> {
            let mut party = PartyBuilder::new(PARTY_0, ch0)
                .register_u64(XRegister::x11, Integer::Public(key_addr))
                .register_u64(XRegister::x12, Integer::Public(nonce_addr))
                .register_u64(XRegister::x13, Integer::Public(pt_addr))
                .register_u64(XRegister::x14, Integer::Public(pt_len))
                .register_u64(XRegister::x15, Integer::Public(ad_addr))
                .register_u64(XRegister::x16, Integer::Public(ad_len))
                .address_range_u64(
                    key_addr,
                    key.iter()
                        .map(|x| Integer::Secret(Share::Binary(*x)))
                        .collect(),
                )?
                .address_range_u64(
                    nonce_addr,
                    nonce
                        .iter()
                        .map(|x| Integer::Secret(Share::Binary(*x)))
                        .collect(),
                )?
                // .n_and_triples(
                //     15 * 12 * 2 + 15 * 6 * pt_len + 15 * 6 * (ad_len + 1) * (ad_len > 0) as u64,
                // )
                .build()?;
            party.execute(&program.parse::<Program>()?.with_entry("encrypt_inplace")?)?;
            let ct = party.address_range_u64(pt_addr..pt_addr + pt_len * U64_BYTES)?;
            let tag = party.address_range_u64(key_addr..key_addr + key_len * U64_BYTES)?;
            Ok(ct.into_iter().chain(tag).collect())
        });

        let party1 = thread::spawn(move || -> Result<Vec<u64>> {
            let mut party = PartyBuilder::new(PARTY_1, ch1)
                .register_u64(XRegister::x11, Integer::Public(key_addr))
                .register_u64(XRegister::x12, Integer::Public(nonce_addr))
                .register_u64(XRegister::x13, Integer::Public(pt_addr))
                .register_u64(XRegister::x14, Integer::Public(pt_len))
                .register_u64(XRegister::x15, Integer::Public(ad_addr))
                .register_u64(XRegister::x16, Integer::Public(ad_len))
                .address_range_u64(
                    pt_addr,
                    pt.iter()
                        .map(|x| Integer::Secret(Share::Binary(*x)))
                        .collect(),
                )?
                .build()?;
            party.execute(&program.parse::<Program>()?.with_entry("encrypt_inplace")?)?;
            let ct = party.address_range_u64(pt_addr..pt_addr + pt_len * U64_BYTES)?;
            let tag = party.address_range_u64(key_addr..key_addr + key_len * U64_BYTES)?;
            Ok(ct.into_iter().chain(tag).collect())
        });

        let res0 = party0.join().unwrap().unwrap();
        let res1 = party1.join().unwrap().unwrap();

        let expected = b"\xbc\x82\x0d\xbd\xf7\xa4\x63\x1c\x5b\x29\x88\x4a\xd6\x91\x75\xc3\xf5\x8e\x28\x43\x6d\xd7\x15\x56\xd5\x8d\xfa\x56\xac\x89\x0b\xeb";

        assert_eq!(u64_arr_to_be_bytes(&res0), expected);
        assert_eq!(u64_arr_to_be_bytes(&res1), expected);

        Ok(())
    }

    fn load(
        w1: &mut [[f64; 784]; 128],
        b1: &mut [f64; 128],
        w2: &mut [[f64; 128]; 10],
        b2: &mut [f64; 10],
        file_path: &str,
    ) -> io::Result<()> {
        let file = File::open(file_path)?;
        let mut reader = BufReader::new(file);

        // read w1
        for row in w1.iter_mut() {
            for value in row.iter_mut() {
                let mut buf = [0u8; 8];
                reader.read_exact(&mut buf)?;
                *value = f64::from_ne_bytes(buf);
            }
        }

        // read b1
        for value in b1.iter_mut() {
            let mut buf = [0u8; 8];
            reader.read_exact(&mut buf)?;
            *value = f64::from_ne_bytes(buf);
        }

        // read w2
        for row in w2.iter_mut() {
            for value in row.iter_mut() {
                let mut buf = [0u8; 8];
                reader.read_exact(&mut buf)?;
                *value = f64::from_ne_bytes(buf);
            }
        }

        // read b2
        for value in b2.iter_mut() {
            let mut buf = [0u8; 8];
            reader.read_exact(&mut buf)?;
            *value = f64::from_ne_bytes(buf);
        }

        Ok(())
    }

    #[test]
    fn mnist_digit_predict() -> Result<()> {
        // https://godbolt.org/z/s8jqK8zvv
        let program = "
            .LCPI0_0:
                    .quad   0xc004000000000000
            .LCPI0_1:
                    .quad   0x4004000000000000
            .LCPI0_2:
                    .quad   0x3ff0000000000000
            .LCPI0_3:
                    .quad   0x3fc999999999999a
            .LCPI0_4:
                    .quad   0x3fe0000000000000
            evaluate:
                    addi    sp, sp, -1040
                    li      a6, 128
                    addi    a7, sp, 16
                    beqz    a6, .LBB0_2
            .LBB0_1:
                    sd      zero, 0(a7)
                    addi    a6, a6, -1
                    addi    a7, a7, 8
                    bnez    a6, .LBB0_1
            .LBB0_2:
                    li      a7, 0
            .Lpcrel_hi0:
                    auipc   a6, %pcrel_hi(.LCPI0_0)
                    fld     fa5, %pcrel_lo(.Lpcrel_hi0)(a6)
                    fmv.d.x fa1, zero
            .Lpcrel_hi1:
                    auipc   a6, %pcrel_hi(.LCPI0_1)
                    fld     fa4, %pcrel_lo(.Lpcrel_hi1)(a6)
            .Lpcrel_hi2:
                    auipc   a6, %pcrel_hi(.LCPI0_2)
                    fld     fa0, %pcrel_lo(.Lpcrel_hi2)(a6)
            .Lpcrel_hi3:
                    auipc   t0, %pcrel_hi(.LCPI0_3)
                    fld     fa3, %pcrel_lo(.Lpcrel_hi3)(t0)
            .Lpcrel_hi4:
                    auipc   t0, %pcrel_hi(.LCPI0_4)
                    fld     fa2, %pcrel_lo(.Lpcrel_hi4)(t0)
                    addi    t0, sp, 16
                    lui     t1, 2
                    addiw   t1, t1, -1920
            .LBB0_3:
                    addi    t2, a7, -128
                    beqz    t2, .LBB0_10
                    slli    t2, a7, 3
                    add     t3, a2, t2
                    fld     ft0, 0(t3)
                    li      t3, 784
                    mv      t4, a1
                    mv      t5, a0
                    beqz    t3, .LBB0_6
            .LBB0_5:
                    fld     ft1, 0(t4)
                    fld     ft2, 0(t5)
                    fmul.d  ft1, ft1, ft2
                    fadd.d  ft0, ft0, ft1
                    addi    t3, t3, -1
                    addi    t5, t5, 8
                    addi    t4, t4, 8
                    bnez    t3, .LBB0_5
            .LBB0_6:
                    flt.d   t3, ft0, fa5
                    fmv.d   ft1, fa1
                    bnez    t3, .LBB0_9
                    flt.d   t3, fa4, ft0
                    fmv.d   ft1, fa0
                    bnez    t3, .LBB0_9
                    fmul.d  ft0, ft0, fa3
                    fadd.d  ft1, ft0, fa2
            .LBB0_9:
                    addi    a7, a7, 1
                    add     t2, t2, t0
                    fsd     ft1, 0(t2)
                    add     a1, a1, t1
                    j       .LBB0_3
            .LBB0_10:
                    fld     fa1, %pcrel_lo(.Lpcrel_hi2)(a6)
                    li      t0, 0
                    li      a6, 10
                    fmv.d.x fa0, zero
                    beq     zero, a6, .LBB0_17
            .LBB0_11:
                    slli    a7, t0, 3
                    add     a0, a4, a7
                    fld     ft0, 0(a0)
                    li      a1, 128
                    addi    a2, sp, 16
                    mv      a0, a3
                    beqz    a1, .LBB0_13
            .LBB0_12:
                    fld     ft1, 0(a0)
                    fld     ft2, 0(a2)
                    fmul.d  ft1, ft1, ft2
                    fadd.d  ft0, ft0, ft1
                    addi    a1, a1, -1
                    addi    a2, a2, 8
                    addi    a0, a0, 8
                    bnez    a1, .LBB0_12
            .LBB0_13:
                    flt.d   a0, ft0, fa5
                    fmv.d   ft1, fa0
                    bnez    a0, .LBB0_16
                    flt.d   a0, fa4, ft0
                    fmv.d   ft1, fa1
                    bnez    a0, .LBB0_16
                    fmul.d  ft0, ft0, fa3
                    fadd.d  ft1, ft0, fa2
            .LBB0_16:
                    addi    t0, t0, 1
                    add     a7, a7, a5
                    fsd     ft1, 0(a7)
                    addi    a3, a3, 1024
                    bne     t0, a6, .LBB0_11
            .LBB0_17:
                    addi    sp, sp, 1040
                    ret
        ";

        let image = "
            ............................
            ............................
            ............................
            ............................
            ....................##......
            ...................###......
            ...................###......
            ..................###.......
            .................###........
            ................###.........
            ...............####.........
            ..............####..........
            .............####...........
            .............###............
            ............####............
            ...........####.............
            ...........###..............
            ..........###...............
            ..........###...............
            .........###................
            ........###.................
            ........###.................
            ........####................
            ........##..................
            ............................
            ............................
            ............................
            ............................
        "
        .trim()
        .lines()
        .flat_map(|row| {
            row.trim()
                .chars()
                .map(|pixel| if pixel == '#' { 1.0 } else { 0.0 })
        })
        .collect::<Vec<f64>>();

        assert_eq!(image.len(), 784);

        let image_len = 784 * U64_BYTES;

        let mut w1 = Box::new([[0.0; 784]; 128]);
        let mut b1 = Box::new([0.0; 128]);
        let mut w2 = Box::new([[0.0; 128]; 10]);
        let mut b2 = Box::new([0.0; 10]);

        load(&mut w1, &mut b1, &mut w2, &mut b2, "data/model.bin").unwrap();

        let w1_len = 784 * 128 * U64_BYTES;
        let b1_len = 128 * U64_BYTES;
        let w2_len = 128 * 10 * U64_BYTES;
        let b2_len = 10 * U64_BYTES;

        let image_addr = 0x0;
        let w1_addr = image_addr + image_len;
        let b1_addr = w1_addr + w1_len;
        let w2_addr = b1_addr + b1_len;
        let b2_addr = w2_addr + w2_len;
        let output_addr = b2_addr + b2_len;

        let (ch0, ch1) = create_channels();

        let party0 = thread::spawn(move || -> Result<Vec<f64>> {
            let mut party = PartyBuilder::new(PARTY_0, ch0)
                .register_u64(XRegister::x10, Integer::Public(image_addr))
                .register_u64(XRegister::x11, Integer::Public(w1_addr))
                .register_u64(XRegister::x12, Integer::Public(b1_addr))
                .register_u64(XRegister::x13, Integer::Public(w2_addr))
                .register_u64(XRegister::x14, Integer::Public(b2_addr))
                .register_u64(XRegister::x15, Integer::Public(output_addr))
                .address_range_f64(
                    w1_addr,
                    w1.iter()
                        .flatten()
                        .map(|x| Float::Secret(x.embed().unwrap()))
                        .collect(),
                )?
                .address_range_f64(
                    b1_addr,
                    b1.iter()
                        .map(|x| Float::Secret(x.embed().unwrap()))
                        .collect(),
                )?
                .address_range_f64(
                    w2_addr,
                    w2.iter()
                        .flatten()
                        .map(|x| Float::Secret(x.embed().unwrap()))
                        .collect(),
                )?
                .address_range_f64(
                    b2_addr,
                    b2.iter()
                        .map(|x| Float::Secret(x.embed().unwrap()))
                        .collect(),
                )?
                .build()?;
            party.execute(&program.parse::<Program>()?.with_entry("evaluate")?)?;
            party.address_range_f64(output_addr..output_addr + U64_BYTES * 10)
        });

        let party1 = thread::spawn(move || -> Result<Vec<f64>> {
            let mut party = PartyBuilder::new(PARTY_1, ch1)
                .register_u64(XRegister::x10, Integer::Public(image_addr))
                .register_u64(XRegister::x11, Integer::Public(w1_addr))
                .register_u64(XRegister::x12, Integer::Public(b1_addr))
                .register_u64(XRegister::x13, Integer::Public(w2_addr))
                .register_u64(XRegister::x14, Integer::Public(b2_addr))
                .register_u64(XRegister::x15, Integer::Public(output_addr))
                .address_range_f64(
                    image_addr,
                    image
                        .iter()
                        .map(|x| Float::Secret(x.embed().unwrap()))
                        .collect(),
                )?
                // .n_mul_triples(784 * 128 + 128 * 10)
                // 13 * 2 for two flt, * 4 for two benz (13 * 2)
                // .n_and_triples(13 * (2 + 4) * (128 + 10))
                .build()?;
            party.execute(&program.parse::<Program>()?.with_entry("evaluate")?)?;
            party.address_range_f64(output_addr..output_addr + U64_BYTES * 10)
        });

        let _ = party0.join().unwrap().unwrap();
        let predictions = party1.join().unwrap().unwrap();

        println!("predictions = {predictions:?}");

        assert_eq!(
            1,
            predictions
                .iter()
                .enumerate()
                .max_by(|(_, a), (_, b)| a.partial_cmp(b).unwrap())
                .map(|(label, _)| label)
                .unwrap()
        );

        Ok(())
    }
}

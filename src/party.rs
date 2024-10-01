use crate::{
    channel::Channel,
    error::{Error, Result},
    instruction::Instruction,
    memory::{Address, Memory},
    mpc_executor::{x_to_shares, MPCExecutor, ToFixedPoint},
    program::Program,
    registers::{FRegisters, Register, VRegisters, XRegister, XRegisters},
    triple_provider::OTTripleProvider,
    types::{Float, Integer, Value},
    FRegister, Label, Share, U64_BYTES,
};
use log::{debug, info};
use serde::{Deserialize, Serialize};
use std::{ops::Range, time::Instant};

/// [`Id`] represents party 0 or party 1.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Id {
    Party0,
    Party1,
}

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
    id: Id,
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
    pub fn new(id: Id, ch: C) -> PartyBuilder<C> {
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

    /// Set a [`XRegister`] to a given pre-shared secret [`Integer`].
    pub fn register_shared_u64(mut self, register: XRegister, integer: Integer) -> PartyBuilder<C> {
        assert!(integer.as_secret().is_some());
        self.x_registers.set(register, integer);
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

    /// Set a [`FRegister`] to a given pre-shared secret [`Float`].
    pub fn register_shared_f64(mut self, register: FRegister, float: Float) -> PartyBuilder<C> {
        assert!(float.as_secret().is_some());
        self.f_registers.set(register, float);
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

    /// Set a [`Address`] to a given pre-shared secret [`Integer`].
    pub fn address_shared_u64(
        mut self,
        address: Address,
        integer: Integer,
    ) -> Result<PartyBuilder<C>> {
        assert!(integer.as_secret().is_some());
        self.memory.store(address, integer.into())?;
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

    /// Set a [`Address`] to a given pre-shared secret [`Float`].
    pub fn address_shared_f64(mut self, address: Address, float: Float) -> Result<PartyBuilder<C>> {
        assert!(float.as_secret().is_some());
        self.memory.store(address, float.into())?;
        Ok(self)
    }

    /// Set a [`Address`] to a given pre-shared secret [`Integer`].
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

    /// Set a [`Address`] range to a given pre-shared [`Vec<Integer>`].
    /// The range is determined by the base `address` and ```inputs.len() * U64_BYTES```.
    pub fn address_range_shared_u64(
        mut self,
        address: Address,
        integers: Vec<Integer>,
    ) -> Result<PartyBuilder<C>> {
        for (i, integer) in integers.into_iter().enumerate() {
            let address = address + i as u64 * U64_BYTES;
            self = self.address_shared_u64(address, integer)?;
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

    /// Set a [`Address`] to a given pre-shared secret [`Vec<Float>`].
    /// The range is determined by the base `address` and ```inputs.len() * U64_BYTES```.
    pub fn address_range_shared_f64(
        mut self,
        address: Address,
        floats: Vec<Float>,
    ) -> Result<PartyBuilder<C>> {
        for (i, float) in floats.into_iter().enumerate() {
            let address = address + i as u64 * U64_BYTES;
            self = self.address_shared_f64(address, float)?;
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
            "party {:?} sending {} inputs",
            self.id,
            self.secret_inputs.len()
        );
        self.ch.send_secret_inputs(&self.secret_inputs)?;
        Ok(())
    }

    /// Receive shares from other party
    fn recv_secret_inputs(&mut self) -> Result<()> {
        debug!("party {:?} receiving inputs", self.id);
        let secret_inputs = self.ch.recv_secret_inputs()?;
        for (location, value) in secret_inputs {
            match location {
                Location::Register(register) => match value {
                    Value::Integer(integer) => self.x_registers.set(register.try_into()?, integer),
                    Value::Float(float) => self.f_registers.set(register.try_into()?, float),
                },
                Location::Address(address) => self.memory.store(address, value)?,
            }
        }
        Ok(())
    }

    /// Construct the [`Party`] instance.
    ///
    /// The setup phase is done in this function, so it can take a long time.
    /// Returned [`Party`] can be used to execute a [`Program`].
    pub fn build(mut self) -> Result<Party<C>> {
        self.send_secret_inputs()?;
        self.recv_secret_inputs()?;

        let mut triple_provider = OTTripleProvider::new(self.id, &mut self.ch)?;
        if self.n_mul_triples > 0 {
            triple_provider.gen_mul_triples(&mut self.ch, self.n_mul_triples)?;
        }
        if self.n_and_triples > 0 {
            triple_provider.gen_and_triples(&mut self.ch, self.n_and_triples)?;
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
    id: Id,
    x_registers: XRegisters,
    f_registers: FRegisters,
    v_registers: VRegisters,
    memory: Memory,
    pc: u64,
    call_depth: u64,
    executor: MPCExecutor<C, OTTripleProvider>,
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
    pub fn register_for_u64(&mut self, register: XRegister, id: Id) -> Result<Option<u64>> {
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
    pub fn register_for_f64(&mut self, register: FRegister, id: Id) -> Result<Option<f64>> {
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
    pub fn address_for_u64(&mut self, address: Address, id: Id) -> Result<Option<u64>> {
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
    pub fn address_for_f64(&mut self, address: Address, id: Id) -> Result<Option<f64>> {
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
        id: Id,
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
        id: Id,
    ) -> Result<Option<Vec<f64>>> {
        debug!("open address range = {range:?}");
        range
            .step_by(8)
            .map(|address| self.address_for_f64(address, id))
            .collect()
    }

    /// Execute the given [`Program`].
    pub fn execute(&mut self, program: &Program) -> Result<()> {
        info!("executing program...");
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
        info!("took {}ms", start.elapsed().as_millis());
        Ok(())
    }
}

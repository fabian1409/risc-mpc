use crate::{
    channel::{Channel, Message},
    error::{Error, Result},
    instruction::Instruction,
    memory::{Address, Memory},
    mpc_executor::{x_to_shares, MPCExecutor, ToFixedPoint},
    program::Program,
    registers::{FRegisters, Register, VRegisters, XRegister, XRegisters},
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
    /// Set a [`Register`] to a given [`Input`].
    pub fn register(mut self, register: Register, input: Input) -> Result<PartyBuilder<C>> {
        match input {
            Input::Integer(Integer::Public(x)) => {
                self.x_registers
                    .set(register.try_into()?, Integer::Public(x));
            }
            Input::Integer(Integer::Secret(secret)) => {
                let (share0, share1) = x_to_shares(secret);
                self.x_registers
                    .set(register.try_into()?, Integer::Secret(share0));
                self.secret_inputs
                    .push((Location::Register(register), Integer::Secret(share1).into()));
            }
            Input::Float(Float::Public(x)) => {
                self.f_registers.set(register.try_into()?, Float::Public(x))
            }
            Input::Float(Float::Secret(secret)) => {
                let (share0, share1) = x_to_shares(Share::Arithmetic(secret));
                self.f_registers
                    .set(register.try_into()?, Float::Secret(share0.into()));
                self.secret_inputs.push((
                    Location::Register(register),
                    Float::Secret(share1.into()).into(),
                ));
            }
        }
        Ok(self)
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
    /// Open the secret value or get the public value as [`Output`] from the given [`Register`].
    pub fn register(&mut self, register: Register) -> Result<Output> {
        let value = match register {
            Register::Integer(x) => self.x_registers.get(x).into(),
            Register::Float(f) => self.f_registers.get(f).into(),
        };
        self.open(value)
    }

    /// Open the secret value (only for [`Party`] with given `id`) or get the public value as [`Output`] from the given [`Register`].
    pub fn register_for(&mut self, register: Register, id: usize) -> Result<Option<Output>> {
        let value = match register {
            Register::Integer(x) => self.x_registers.get(x).into(),
            Register::Float(f) => self.f_registers.get(f).into(),
        };
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
                    let address = program.offset(label, self.pc)?;
                    self.update_pc(address, 0);
                    self.call_depth += 1;
                }
                Instruction::JALR { rd, rs1, offset } => {
                    self.x_registers.set(*rd, Integer::Public(self.pc + 1));
                    let base = self.x_registers.get(*rs1);
                    if let Integer::Public(base) = base {
                        self.update_pc(base, *offset);
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
                        let address = program.offset(label, self.pc)?;
                        self.update_pc(address, 0);
                    }
                }
                Instruction::BNE { rs1, rs2, label } => {
                    let rs1 = self.x_registers.get(*rs1);
                    let rs2 = self.x_registers.get(*rs2);
                    let eq = self.executor.beq(rs1, rs2)?;
                    if !eq {
                        debug!("bne taking branch");
                        let address = program.offset(label, self.pc)?;
                        self.update_pc(address, 0);
                    }
                }
                Instruction::BLT { rs1, rs2, label } => {
                    let rs1 = self.x_registers.get(*rs1);
                    let rs2 = self.x_registers.get(*rs2);
                    let lt = self.executor.blt(rs1, rs2)?;
                    if lt {
                        debug!("blt taking branch");
                        let address = program.offset(label, self.pc)?;
                        self.update_pc(address, 0);
                    }
                }
                Instruction::BGE { rs1, rs2, label } => {
                    let rs1 = self.x_registers.get(*rs1);
                    let rs2 = self.x_registers.get(*rs2);
                    let lt = self.executor.blt(rs1, rs2)?;
                    if !lt {
                        debug!("bge taking branch");
                        let address = program.offset(label, self.pc)?;
                        self.update_pc(address, 0);
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
                Instruction::AUIPC { rd, imm } => {
                    let address = if imm.is_negative() {
                        self.pc - ((imm.wrapping_abs() as u64) << 12)
                    } else {
                        self.pc + ((*imm as u64) << 12)
                    };
                    self.x_registers.set(*rd, Integer::Public(address));
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
                        let address = program.offset(label, self.pc)?;
                        self.update_pc(address, 0);
                    }
                }
                Instruction::BNEZ { rs1, label } => {
                    let rs1 = self.x_registers.get(*rs1);
                    let eq = self.executor.beq(rs1, Integer::Public(0))?;
                    if !eq {
                        debug!("bnez taking branch");
                        let address = program.offset(label, self.pc)?;
                        self.update_pc(address, 0);
                    }
                }
                Instruction::BLEZ { rs1, label } => {
                    let rs1 = self.x_registers.get(*rs1);
                    let le = self.executor.ble(rs1, Integer::Public(0))?;
                    if le {
                        debug!("blez taking branch");
                        let address = program.offset(label, self.pc)?;
                        self.update_pc(address, 0);
                    }
                }
                Instruction::BGEZ { rs1, label } => {
                    let rs1 = self.x_registers.get(*rs1);
                    let ge = self.executor.bge(rs1, Integer::Public(0))?;
                    if ge {
                        debug!("bgez taking branch");
                        let address = program.offset(label, self.pc)?;
                        self.update_pc(address, 0);
                    }
                }
                Instruction::BLTZ { rs1, label } => {
                    let rs1 = self.x_registers.get(*rs1);
                    let lt = self.executor.blt(rs1, Integer::Public(0))?;
                    if lt {
                        debug!("bltz taking branch");
                        let address = program.offset(label, self.pc)?;
                        self.update_pc(address, 0);
                    }
                }
                Instruction::BGTZ { rs1, label } => {
                    let rs1 = self.x_registers.get(*rs1);
                    let gt = self.executor.bgt(rs1, Integer::Public(0))?;
                    if gt {
                        debug!("bgtz taking branch");
                        let address = program.offset(label, self.pc)?;
                        self.update_pc(address, 0);
                    }
                }
                Instruction::BGT { rs1, rs2, label } => {
                    let rs1 = self.x_registers.get(*rs1);
                    let rs2 = self.x_registers.get(*rs2);
                    let gt = self.executor.bgt(rs1, rs2)?;
                    if gt {
                        debug!("bgt taking branch");
                        let address = program.offset(label, self.pc)?;
                        self.update_pc(address, 0);
                    }
                }
                Instruction::BLE { rs1, rs2, label } => {
                    let rs1 = self.x_registers.get(*rs1);
                    let rs2 = self.x_registers.get(*rs2);
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
                    if let Integer::Public(address) = self.x_registers.get(*rs1) {
                        debug!("jump to {address}");
                        self.update_pc(address, 0);
                    } else {
                        return Err(Error::SecretValueAsAddress);
                    }
                }
                Instruction::RET => {
                    if let Integer::Public(address) = self.x_registers.get(XRegister::x1) {
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
                    self.x_registers
                        .set(XRegister::x1, Integer::Public(self.pc));
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
    use super::{PartyBuilder, PARTY_0};
    use crate::{
        channel::{Message, ThreadChannel},
        party::PARTY_1,
        registers::XRegister,
        types::Integer,
        Program, Result, Share, U64_BYTES,
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
                .register(XRegister::x10.into(), Integer::Public(5).into())?
                .build()?;
            party.execute(&program.parse()?)?;
            party.register(XRegister::x10.into())?.try_into()
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
                .register(XRegister::x10.into(), Integer::Public(10).into())?
                .build()?;
            party.execute(&program.parse()?)?;
            party.register(XRegister::x10.into())?.try_into()
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
                .register(XRegister::x10.into(), Integer::Public(set0_address).into())?
                .register(XRegister::x11.into(), Integer::Public(set0_len).into())?
                .register(XRegister::x12.into(), Integer::Public(set1_address).into())?
                .register(XRegister::x13.into(), Integer::Public(set1_len).into())?
                .register(
                    XRegister::x14.into(),
                    Integer::Public(intersection_addr).into(),
                )?
                .address_range(
                    set_address,
                    set.iter()
                        .map(|x| Integer::Secret(Share::Arithmetic(*x)).into())
                        .collect(),
                )?
                .build()?;

            party.execute(&program.parse()?)?;

            let len: u64 = party.register(XRegister::x10.into())?.try_into()?;

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
                .register(XRegister::x10.into(), Integer::Public(sal0_addr).into())?
                .register(XRegister::x11.into(), Integer::Public(sal0_len).into())?
                .register(XRegister::x12.into(), Integer::Public(sal1_addr).into())?
                .register(XRegister::x13.into(), Integer::Public(sal1_len).into())?
                .address_range(
                    salaries_address,
                    salaries
                        .iter()
                        .map(|x| Integer::Secret(Share::Arithmetic(*x)).into())
                        .collect(),
                )?
                .build()?;

            party.execute(&program.parse::<Program>()?.with_entry("mean")?)?;

            party.register(XRegister::x10.into())?.try_into()
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
                    .register(XRegister::x10.into(), Integer::Public(0x0).into())?
                    .register(XRegister::x11.into(), Integer::Public(U64_BYTES * 5).into())?
                    .register(XRegister::x12.into(), Integer::Public(0x1f).into())?
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
                    .register(XRegister::x10.into(), Integer::Public(0x0).into())?
                    .register(XRegister::x11.into(), Integer::Public(U64_BYTES * 5).into())?
                    .register(XRegister::x12.into(), Integer::Public(0x1f).into())?
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

    #[test]
    fn vec_mul() -> Result<()> {
        let program = "
            vsetvli  x0,a3,e64
            vle.v    v0,a0
            vle.v    v1,a1
            vmul.vv  v0,v0,v1
            vse.v    v0,a2
        ";

        let (ch0, ch1) = create_channels();
        let run = move |id: usize,
                        ch: ThreadChannel,
                        vec: &[u64],
                        vec_address: u64|
              -> Result<Vec<u64>> {
            let mut party = PartyBuilder::new(id, ch)
                .register(XRegister::x10.into(), Integer::Public(0x0).into())?
                .register(XRegister::x11.into(), Integer::Public(U64_BYTES * 4).into())?
                .register(XRegister::x12.into(), Integer::Public(U64_BYTES * 8).into())?
                .register(XRegister::x13.into(), Integer::Public(4).into())?
                .address_range(
                    vec_address,
                    vec.iter()
                        .map(|x| Integer::Secret(Share::Arithmetic(*x)).into())
                        .collect(),
                )?
                .build()?;
            party.execute(&program.parse()?)?;
            party
                .address_range(U64_BYTES * 8..U64_BYTES * 12)?
                .into_iter()
                .map(TryInto::try_into)
                .collect::<Result<Vec<u64>>>()
        };
        let vec0 = vec![2, 2, 2, 4];
        let vec1 = vec![2, 4, 8, 8];
        let party0 = thread::spawn(move || run(PARTY_0, ch0, &vec0, 0));
        let party1 = thread::spawn(move || run(PARTY_1, ch1, &vec1, U64_BYTES * 4));

        let res0 = party0.join().unwrap().unwrap();
        let res1 = party1.join().unwrap().unwrap();

        assert_eq!(res0, vec![4, 8, 16, 32]);
        assert_eq!(res1, vec![4, 8, 16, 32]);

        Ok(())
    }
}

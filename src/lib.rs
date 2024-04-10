//! riscMPC: general-purpose multi-party computation from RISC-V assembly.
//!
//! # Example: mean wage
//!
//! This examples shows how to compute the mean salary without revealing salaries to the other party.
//! The code for both parties can be found in the `examples` directory.
//!
//! ```no_run
#![doc = include_str!("../examples/mean_salary_party0.rs")]
//! ```

mod channel;
mod error;
mod instruction;
mod memory;
mod mpc_executor;
mod ot;
mod party;
mod registers;
mod triple_provider;
mod types;

pub use channel::{TcpChannel, ThreadChannel};
pub use error::Result;
pub use instruction::{Instruction, Label, Program};
pub use memory::{Address, U64_BYTES};
pub use mpc_executor::CMP_AND_TRIPLES;
pub use party::{Party, PartyBuilder, PARTY_0, PARTY_1};
pub use registers::Register;
pub use types::{Share, Value};

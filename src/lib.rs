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
mod program;
mod registers;
mod triple_provider;
mod types;

pub use channel::{Channel, TcpChannel, ThreadChannel};
pub use error::Result;
pub use instruction::{Instruction, Label};
pub use memory::{Address, U64_BYTES};
pub use mpc_executor::{EmbedFixedPoint, A2B_AND_TRIPLES};
pub use party::{Id, Party, PartyBuilder};
pub use program::Program;
pub use registers::{FRegister, Register, XRegister};
pub use types::{Float, Integer, Share};

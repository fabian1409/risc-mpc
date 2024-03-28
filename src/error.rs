use thiserror::Error;

/// The error type for riscMPC
#[allow(clippy::enum_variant_names)]
#[derive(Debug, Error)]
pub enum Error {
    #[error("shares have different types")]
    DifferentShareTypes,
    #[error("invalid instruction {0}")]
    ParseInstructionError(String),
    #[error("invalid offset {0}")]
    ParseOffsetError(String),
    #[error("invalid integer {0}")]
    ParseIntError(#[from] std::num::ParseIntError),
    #[error("invalid register {0}")]
    ParseRegisterError(String),
    #[error("invalid party id {0}")]
    InvalidPartyId(usize),
    #[error(transparent)]
    ChannelError(#[from] crate::channel::error::Error),
    #[error("tried to divide by 0")]
    DivByZero,
    #[error("failed to get triple")]
    BeaverTripleError,
    #[error("tried to divide by secret value")]
    DivBySecretValue,
    #[error("tried to shift by secret value")]
    ShiftBySecretValue,
    #[error("tried to use secret value as address")]
    SecretValueAsAddress,
    #[error("address {0} is not 8-byte aligned")]
    AddressNotAligned(u64),
    #[error("unknown label {0}")]
    UnknownLabel(String),
}

/// [`Result`] type with riscMPC [`enum@Error`] type.
pub type Result<T> = std::result::Result<T, Error>;

use crate::error::{Error, Result};
use serde::{Deserialize, Serialize};

/// [`Share`] represents either a [`Arithmetic`] or [`Binary`] share.
///
/// [`Arithmetic`]: Share::Arithmetic
/// [`Binary`]: Share::Binary
#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub enum Share {
    Arithmetic(u64),
    Binary(u64),
}

impl From<Share> for u64 {
    fn from(value: Share) -> Self {
        match value {
            Share::Arithmetic(v) => v,
            Share::Binary(v) => v,
        }
    }
}

/// [`Integer`] represents either a [`Public`] or [`Secret`] integer.
///
/// [`Public`]: Integer::Public
/// [`Secret`]: Integer::Secret
#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub enum Integer {
    Secret(Share),
    Public(u64),
}

impl Integer {
    pub fn as_u64(&self) -> u64 {
        match self {
            Integer::Secret(Share::Arithmetic(x)) => *x,
            Integer::Secret(Share::Binary(x)) => *x,
            Integer::Public(x) => *x,
        }
    }

    pub fn as_public(&self) -> Option<u64> {
        match self {
            Integer::Public(x) => Some(*x),
            _ => None,
        }
    }

    pub fn as_secret(&self) -> Option<Share> {
        match self {
            Integer::Secret(share) => Some(*share),
            _ => None,
        }
    }
}

impl Default for Integer {
    fn default() -> Self {
        Self::Public(0)
    }
}

/// [`Float`] represents either a [`Secret`] or [`Public`] float.
///
/// [`Secret`]: Float::Secret
/// [`Public`]: Float::Public
#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub enum Float {
    Secret(u64),
    Public(f64),
}

impl Float {
    pub fn as_secret(&self) -> Option<u64> {
        match self {
            Float::Secret(x) => Some(*x),
            _ => None,
        }
    }

    pub fn as_public(&self) -> Option<f64> {
        match self {
            Float::Public(x) => Some(*x),
            _ => None,
        }
    }
}

impl Default for Float {
    fn default() -> Self {
        Self::Public(0.0)
    }
}

/// [`Value`] represents either a [`Integer`] or [`Float`] value.
///
/// [`Integer`]: Value::Integer
/// [`Float`]: Value::Float
#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub enum Value {
    Integer(Integer),
    Float(Float),
}

impl Value {
    pub fn as_public_integer(&self) -> Option<u64> {
        match self {
            Value::Integer(Integer::Public(x)) => Some(*x),
            _ => None,
        }
    }
}

impl Default for Value {
    fn default() -> Self {
        Value::Integer(Integer::Public(0))
    }
}

impl TryInto<Integer> for Value {
    type Error = Error;

    fn try_into(self) -> Result<Integer> {
        match self {
            Value::Integer(integer) => Ok(integer),
            Value::Float(_) => Err(Error::UnexpectedValue),
        }
    }
}

impl TryInto<Float> for Value {
    type Error = Error;

    fn try_into(self) -> Result<Float> {
        match self {
            Value::Integer(_) => Err(Error::UnexpectedValue),
            Value::Float(float) => Ok(float),
        }
    }
}

impl From<Integer> for Value {
    fn from(value: Integer) -> Self {
        Value::Integer(value)
    }
}

impl From<Float> for Value {
    fn from(value: Float) -> Self {
        Value::Float(value)
    }
}

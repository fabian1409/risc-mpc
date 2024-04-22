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

/// [`Value`] represents either a [`Public`] or [`Secret`] value.
///
/// [`Public`]: Value::Public
/// [`Secret`]: Value::Secret
#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub enum Value {
    Secret(Share),
    Public(u64),
}

impl Value {
    pub fn as_public(&self) -> Option<u64> {
        match self {
            Value::Secret(_) => None,
            Value::Public(x) => Some(*x),
        }
    }
}

impl From<Value> for u64 {
    fn from(value: Value) -> Self {
        match value {
            Value::Public(v) => v,
            Value::Secret(share) => share.into(),
        }
    }
}

impl Default for Value {
    fn default() -> Self {
        Self::Public(0)
    }
}

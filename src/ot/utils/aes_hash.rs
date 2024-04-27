//! Correlation robust AES hash.
//!
//! This implementation of a correlation robust AES hash function
//! is based on the findings of <https://eprint.iacr.org/2019/074>.
//!
//! Based on <https://github.com/encryptogroup/FLUTE/blob/main/crates/zappot/src/util/aes_hash.rs>.

use super::block::Block;
use aes::cipher::{BlockEncrypt, Key, KeyInit};
use aes::Aes128;

pub const FIXED_KEY: u128 = 193502124791825095790518994062991136444;

#[derive(Debug)]
pub struct AesHash {
    aes: Aes128,
}

impl AesHash {
    /// Create a new `AesHash` with the given key.
    pub fn new(key: &Key<Aes128>) -> Self {
        Self {
            aes: Aes128::new(key),
        }
    }

    /// Compute the correlation robust hash of a block.
    ///
    /// # Warning: only secure in semi-honest setting!
    /// See <https://eprint.iacr.org/2019/074> for details.
    pub fn cr_hash(&self, x: Block) -> Block {
        let mut x_enc = x.to_le_bytes().into();
        self.aes.encrypt_block(&mut x_enc);
        x ^ Block::from_le_bytes(x_enc.into())
    }
}

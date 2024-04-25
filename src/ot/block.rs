use curve25519_dalek::RistrettoPoint;
use tiny_keccak::{Hasher, IntoXof, KangarooTwelve, Xof};

pub type Block = u128;

#[inline]
pub fn hash_pt(seed: u128, pt: &RistrettoPoint) -> Block {
    let mut hasher = KangarooTwelve::new(seed.to_le_bytes());
    hasher.update(pt.compress().as_bytes());
    let mut xof = hasher.into_xof();
    let mut digest = [0; 16];
    xof.squeeze(&mut digest);
    Block::from_le_bytes(digest)
}

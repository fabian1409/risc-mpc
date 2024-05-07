//! Based on <https://github.com/GaloisInc/swanky/blob/dev/ocelot/src/utils.rs>.

use std::arch::x86_64::{_mm_movemask_epi8, _mm_setr_epi8, _mm_slli_epi64};

pub mod aes_hash;
pub mod aes_rng;
pub mod block;

#[inline]
pub fn boolvec_to_u8vec(bv: &[bool]) -> Vec<u8> {
    let offset = if bv.len() % 8 == 0 { 0 } else { 1 };
    let mut v = vec![0u8; bv.len() / 8 + offset];
    for (i, b) in bv.iter().enumerate() {
        v[i / 8] |= (*b as u8) << (i % 8);
    }
    v
}

#[inline]
pub fn u8vec_to_boolvec(v: &[u8]) -> Vec<bool> {
    let mut bv = Vec::with_capacity(v.len() * 8);
    for byte in v {
        for i in 0..8 {
            bv.push((1 << i) & byte != 0);
        }
    }
    bv
}

#[inline]
pub fn xor_inplace(a: &mut [u8], b: &[u8]) {
    for (a, b) in a.iter_mut().zip(b.iter()) {
        *a ^= *b;
    }
}

#[inline]
pub fn transpose(input: &[u8], nrows: usize, ncols: usize) -> Vec<u8> {
    assert_eq!(nrows % 16, 0);
    assert_eq!(ncols % 8, 0);
    let mut output = vec![0u8; nrows * ncols / 8];

    let inp = |x: usize, y: usize| -> usize { x * ncols / 8 + y / 8 };
    let out = |x: usize, y: usize| -> usize { y * nrows / 8 + x / 8 };

    unsafe {
        let mut v;
        for rr in (0..=nrows - 16).step_by(16) {
            for cc in (0..ncols).step_by(8) {
                v = _mm_setr_epi8(
                    *input.get_unchecked(inp(rr, cc)) as i8,
                    *input.get_unchecked(inp(rr + 1, cc)) as i8,
                    *input.get_unchecked(inp(rr + 2, cc)) as i8,
                    *input.get_unchecked(inp(rr + 3, cc)) as i8,
                    *input.get_unchecked(inp(rr + 4, cc)) as i8,
                    *input.get_unchecked(inp(rr + 5, cc)) as i8,
                    *input.get_unchecked(inp(rr + 6, cc)) as i8,
                    *input.get_unchecked(inp(rr + 7, cc)) as i8,
                    *input.get_unchecked(inp(rr + 8, cc)) as i8,
                    *input.get_unchecked(inp(rr + 9, cc)) as i8,
                    *input.get_unchecked(inp(rr + 10, cc)) as i8,
                    *input.get_unchecked(inp(rr + 11, cc)) as i8,
                    *input.get_unchecked(inp(rr + 12, cc)) as i8,
                    *input.get_unchecked(inp(rr + 13, cc)) as i8,
                    *input.get_unchecked(inp(rr + 14, cc)) as i8,
                    *input.get_unchecked(inp(rr + 15, cc)) as i8,
                );

                for i in (0..8).rev() {
                    let j = out(rr, cc + i);
                    output
                        .get_unchecked_mut(j..=j + 1)
                        .copy_from_slice(&(_mm_movemask_epi8(v) as i16).to_le_bytes());
                    v = _mm_slli_epi64::<1>(v);
                }
            }
        }
    };
    output
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test(nrows: usize, ncols: usize) {
        let m = (0..nrows * ncols / 8)
            .map(|_| rand::random::<u8>())
            .collect::<Vec<u8>>();
        let m_ = m.clone();
        let m = transpose(&m, nrows, ncols);
        let m = transpose(&m, ncols, nrows);
        assert_eq!(m, m_);
    }

    #[test]
    fn test_transpose() {
        test(16, 16);
        test(128, 16);
        test(128, 24);
        test(128, 128);
        test(128, 1 << 16);
        test(128, 1 << 18);
        test(32, 32);
        test(64, 64);
    }

    #[test]
    fn test_boolvec_to_u8vec() {
        let v = (0..128)
            .map(|_| rand::random::<bool>())
            .collect::<Vec<bool>>();
        let v_ = boolvec_to_u8vec(&v);
        let v__ = u8vec_to_boolvec(&v_);
        assert_eq!(v, v__);
    }

    #[test]
    fn test_u8vec_to_boolvec() {
        let v = (0..128).map(|_| rand::random::<u8>()).collect::<Vec<u8>>();
        let v_ = u8vec_to_boolvec(&v);
        let v__ = boolvec_to_u8vec(&v_);
        assert_eq!(v, v__);
    }
}

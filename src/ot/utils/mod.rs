//! Based on <https://github.com/GaloisInc/swanky/blob/dev/ocelot/src/utils.rs>.

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

#[inline(always)]
pub fn xor_inplace(a: &mut [u8], b: &[u8]) {
    for (a, b) in a.iter_mut().zip(b.iter()) {
        *a ^= *b;
    }
}

#[inline]
#[cfg(target_arch = "x86_64")]
pub fn transpose(m: &[u8], nrows: usize, ncols: usize) -> Vec<u8> {
    unsafe {
        let mut m_ = vec![0u8; nrows * ncols / 8];
        _transpose(m_.as_mut_ptr(), m.as_ptr(), nrows as u64, ncols as u64);
        m_
    }
}

#[inline(always)]
#[cfg(target_arch = "x86_64")]
unsafe fn _transpose(out: *mut u8, inp: *const u8, nrows: u64, ncols: u64) {
    assert!(nrows >= 16);
    assert_eq!(nrows % 8, 0);
    assert_eq!(ncols % 8, 0);
    sse_trans(out, inp, nrows, ncols)
}

#[link(name = "transpose")]
#[cfg(target_arch = "x86_64")]
extern "C" {
    fn sse_trans(out: *mut u8, inp: *const u8, nrows: u64, ncols: u64);
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
        test(24, 16);
        test(32, 16);
        test(40, 16);
        test(128, 16);
        test(128, 24);
        test(128, 128);
        test(128, 1 << 16);
        test(128, 1 << 18);
        test(32, 32);
        test(64, 32);
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

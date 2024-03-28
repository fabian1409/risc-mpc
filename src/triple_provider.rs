#![allow(dead_code, unused_imports)]

use crate::{
    channel::Channel,
    error::{Error, Result},
    ot::{OTReceiver, OTSender},
    party::{PARTY_0, PARTY_1},
};
use bit::BitIndex;
use log::{debug, info};
use rand::Rng;
use rug::Integer;
use std::time::Instant;

pub type Triple = (u64, u64, u64);

#[derive(Debug)]
pub struct TripleProvider {
    id: usize,
    mul_triple_pool: Vec<(u64, u64, u64)>,
    and_triple_pool: Vec<(u64, u64, u64)>,
}

impl TripleProvider {
    pub fn new(id: usize) -> TripleProvider {
        TripleProvider {
            id,
            mul_triple_pool: Vec::new(),
            and_triple_pool: Vec::new(),
        }
    }

    pub fn setup<C: Channel>(
        &mut self,
        ch: &mut C,
        n_mul_triples: u64,
        n_and_triples: u64,
    ) -> Result<()> {
        info!("starting setup phase");
        let start = Instant::now();
        for i in 0..n_mul_triples {
            debug!("generating mul triple {i}");
            let mt = self.gen_mult_triple(ch)?;
            self.mul_triple_pool.push(mt);
        }

        for i in 0..n_and_triples {
            debug!("generating and triple {i}");
            let at = self.gen_and_triple(ch)?;
            self.and_triple_pool.push(at);
        }
        let duration = start.elapsed();
        info!("setup done, took {}ms", duration.as_millis());
        Ok(())
    }

    #[cfg(not(test))]
    pub fn mul_triple(&mut self) -> Option<Triple> {
        self.mul_triple_pool.pop()
    }

    #[cfg(test)]
    pub fn mul_triple(&mut self) -> Option<Triple> {
        Some(Triple::default())
    }

    #[cfg(not(test))]
    pub fn and_triple(&mut self) -> Option<Triple> {
        self.and_triple_pool.pop()
    }

    #[cfg(test)]
    pub fn and_triple(&mut self) -> Option<Triple> {
        Some(Triple::default())
    }

    // https://link.springer.com/content/pdf/10.1007/3-540-48405-1_8.pdf
    fn ot_mul<C: Channel>(
        &mut self,
        ch: &mut C,
        a_share: u64,
        b_share: u64,
        sender: usize,
    ) -> Result<u64> {
        let mut rng = rand::thread_rng();
        if self.id == sender {
            let mut sender = OTSender::new();
            let mut c0 = 0u64;
            let mut ss = Vec::new();
            for _ in 0..64 {
                let tmp = rng.gen();
                c0 = c0.wrapping_add(tmp);
                ss.push(Integer::from(tmp));
            }
            let c0 = -(c0 as i128) as u64;
            let mut inputs = Vec::new();
            for (i, s) in ss.into_iter().enumerate() {
                inputs.push((
                    s.clone(),
                    (2u128.pow(i as u32) * Integer::from(a_share) + s)
                        % Integer::from(2u128.pow(64)),
                ));
            }
            sender.send(ch, &inputs)?;
            Ok(c0)
        } else {
            let mut receiver = OTReceiver::new();
            let mut choices = Vec::new();
            for i in 0..64 {
                choices.push(b_share.bit(i));
            }
            let res = receiver.receive(ch, &choices)?;
            let mut c1 = 0u64;
            for e in res {
                c1 = c1.wrapping_add(e.try_into().unwrap());
            }
            Ok(c1)
        }
    }

    // https://encrypto.de/papers/DSZ15.pdf
    fn gen_mult_triple<C: Channel>(&mut self, ch: &mut C) -> Result<(u64, u64, u64)> {
        let mut rng = rand::thread_rng();
        let a_share = rng.gen();
        let b_share = rng.gen();
        let u_share = self.ot_mul(ch, a_share, b_share, PARTY_0)?;
        let v_share = self.ot_mul(ch, a_share, b_share, PARTY_1)?;
        let c_share = a_share
            .wrapping_mul(b_share)
            .wrapping_add(u_share)
            .wrapping_add(v_share);
        debug!("a_share = {a_share} b_share = {b_share} c_share = {c_share}");
        Ok((a_share, b_share, c_share))
    }

    fn ot_rand_ab_uv<C: Channel>(&mut self, ch: &mut C, sender: usize) -> Result<(u64, u64)> {
        let mut rng = rand::thread_rng();
        if self.id == sender {
            let mut inputs = Vec::new();
            let mut b = 0u64;
            let mut v = 0u64;
            for i in 0..64 {
                let xi0: bool = rng.gen();
                let xi1: bool = rng.gen();
                b.set_bit(i, xi0 ^ xi1);
                v.set_bit(i, xi0);
                inputs.push((Integer::from(xi0), Integer::from(xi1)));
            }
            let mut sender = OTSender::new();
            sender.send(ch, &inputs)?;
            Ok((b, v))
        } else {
            let a: u64 = rng.gen();
            let mut choices = Vec::new();
            for i in 0..64 {
                choices.push(a.bit(i));
            }
            let mut receiver = OTReceiver::new();
            let xa = receiver.receive(ch, &choices)?;
            let mut u = 0u64;
            for (i, x) in xa.iter().enumerate() {
                u.set_bit(i, *x != Integer::ZERO);
            }
            Ok((a, u))
        }
    }

    fn gen_and_triple<C: Channel>(&mut self, ch: &mut C) -> Result<(u64, u64, u64)> {
        if self.id == PARTY_0 {
            let (a, u) = self.ot_rand_ab_uv(ch, PARTY_1)?;
            let (b, v) = self.ot_rand_ab_uv(ch, PARTY_0)?;
            let c = (a & b) ^ u ^ v;
            Ok((a, b, c))
        } else {
            let (b, v) = self.ot_rand_ab_uv(ch, PARTY_1)?;
            let (a, u) = self.ot_rand_ab_uv(ch, PARTY_0)?;
            let c = (a & b) ^ u ^ v;
            Ok((a, b, c))
        }
    }
}

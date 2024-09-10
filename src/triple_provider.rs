use crate::{
    channel::Channel,
    error::Result,
    ot::{
        alsz::{OTExtReceiver, OTExtSender},
        utils::block::Block,
    },
    party::{PARTY_0, PARTY_1},
};
use bit::BitIndex;
use itertools::izip;
use log::{debug, info};
use rand::Rng;
use std::time::Instant;

pub type Triple = (u64, u64, u64);

#[derive(Debug)]
pub struct TripleProvider {
    id: usize,
    sender: OTExtSender,
    receiver: OTExtReceiver,
    mul_triple_pool: Vec<(u64, u64, u64)>,
    and_triple_pool: Vec<(u64, u64, u64)>,
}

impl TripleProvider {
    pub fn new<C: Channel>(id: usize, ch: &mut C) -> Result<TripleProvider> {
        let (sender, receiver) = if id == PARTY_0 {
            let sender = OTExtSender::new(ch)?;
            let receiver = OTExtReceiver::new(ch)?;
            (sender, receiver)
        } else {
            let receiver = OTExtReceiver::new(ch)?;
            let sender = OTExtSender::new(ch)?;
            (sender, receiver)
        };
        Ok(TripleProvider {
            id,
            sender,
            receiver,
            mul_triple_pool: Vec::new(),
            and_triple_pool: Vec::new(),
        })
    }

    pub fn setup<C: Channel>(
        &mut self,
        ch: &mut C,
        n_mul_triples: u64,
        n_and_triples: u64,
    ) -> Result<()> {
        let start = Instant::now();

        debug!("generating {n_mul_triples} mul-triples");
        self.mul_triple_pool = self.gen_mul_triples(ch, n_mul_triples)?;

        debug!("generating {n_and_triples} and-triples");
        self.and_triple_pool = self.gen_and_triples(ch, n_and_triples)?;

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
        a_shares: &[u64],
        b_shares: &[u64],
        sender: usize,
    ) -> Result<Vec<u64>> {
        let mut rng = rand::thread_rng();
        if self.id == sender {
            let mut c0s = Vec::with_capacity(a_shares.len());
            let mut inputs = Vec::with_capacity(64 * a_shares.len());
            for a_share in a_shares {
                let mut c0 = 0u64;
                let mut ss = Vec::new();
                for _ in 0..64 {
                    let tmp = rng.gen();
                    c0 = c0.wrapping_add(tmp);
                    ss.push(Block::from(tmp));
                }
                let c0 = -(c0 as i128) as u64;
                c0s.push(c0);
                for (i, s) in ss.into_iter().enumerate() {
                    inputs.push((
                        s,
                        (2u128.pow(i as u32) * Block::from(*a_share) + s)
                            % Block::from(2u128.pow(64)),
                    ));
                }
            }
            self.sender.send(ch, &inputs)?;
            Ok(c0s)
        } else {
            let mut choices = Vec::with_capacity(64 * b_shares.len());
            let mut c1s = Vec::with_capacity(b_shares.len());
            for b_share in b_shares {
                for i in 0..64 {
                    choices.push(b_share.bit(i));
                }
            }
            let res = self.receiver.receive(ch, &choices)?;
            for es in res.chunks_exact(64) {
                let mut c1 = 0u64;
                for e in es {
                    c1 = c1.wrapping_add((*e).try_into().unwrap());
                }
                c1s.push(c1);
            }
            Ok(c1s)
        }
    }

    // https://encrypto.de/papers/DSZ15.pdf
    fn gen_mul_triples<C: Channel>(
        &mut self,
        ch: &mut C,
        n_mul_triples: u64,
    ) -> Result<Vec<(u64, u64, u64)>> {
        let mut rng = rand::thread_rng();
        let a_shares = (0..n_mul_triples).map(|_| rng.gen()).collect::<Vec<u64>>();
        let b_shares = (0..n_mul_triples).map(|_| rng.gen()).collect::<Vec<u64>>();
        let u_shares = self.ot_mul(ch, &a_shares, &b_shares, PARTY_0)?;
        let v_shares = self.ot_mul(ch, &a_shares, &b_shares, PARTY_1)?;
        let triples = izip!(a_shares, b_shares, u_shares, v_shares)
            .map(|(a, b, u, v)| (a, b, a.wrapping_mul(b).wrapping_add(u).wrapping_add(v)))
            .collect();
        Ok(triples)
    }

    fn ot_rand_ab_uv<C: Channel>(
        &mut self,
        ch: &mut C,
        sender: usize,
        n_and_triples: u64,
    ) -> Result<Vec<(u64, u64)>> {
        let mut rng = rand::thread_rng();
        if self.id == sender {
            let mut bvs = Vec::with_capacity(n_and_triples as usize);
            let mut inputs = Vec::with_capacity(64 * n_and_triples as usize);
            for _ in 0..n_and_triples {
                let mut b = 0u64;
                let mut v = 0u64;
                for i in 0..64 {
                    let xi0: bool = rng.gen();
                    let xi1: bool = rng.gen();
                    b.set_bit(i, xi0 ^ xi1);
                    v.set_bit(i, xi0);
                    inputs.push((Block::from(xi0), Block::from(xi1)));
                }
                bvs.push((b, v));
            }
            self.sender.send(ch, &inputs)?;
            Ok(bvs)
        } else {
            let mut aus = Vec::with_capacity(n_and_triples as usize);
            let mut choices = Vec::with_capacity(64 * n_and_triples as usize);
            for _ in 0..n_and_triples {
                let a: u64 = rng.gen();
                for i in 0..64 {
                    choices.push(a.bit(i));
                }
                aus.push((a, 0));
            }
            let xas = self.receiver.receive(ch, &choices)?;
            for (xa, au) in xas.chunks_exact(64).zip(aus.iter_mut()) {
                let mut u = 0u64;
                for (i, x) in xa.iter().enumerate() {
                    u.set_bit(i, *x != 0);
                }
                au.1 = u;
            }
            Ok(aus)
        }
    }

    fn gen_and_triples<C: Channel>(
        &mut self,
        ch: &mut C,
        n_and_triples: u64,
    ) -> Result<Vec<(u64, u64, u64)>> {
        let aus = self.ot_rand_ab_uv(ch, PARTY_1, n_and_triples)?;
        let bvs = self.ot_rand_ab_uv(ch, PARTY_0, n_and_triples)?;
        let triples = aus
            .into_iter()
            .zip(bvs)
            .map(|((a, u), (b, v))| (a, b, (a & b) ^ u ^ v))
            .collect();
        Ok(triples)
    }
}

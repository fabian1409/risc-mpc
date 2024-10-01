use crate::{
    channel::Channel,
    error::{Error, Result},
    ot::{
        chou_orlandi::{OTReceiver, OTSender},
        utils::block::Block,
    },
    party::Id,
    triple_provider::TripleProvider,
    types::{Float, Integer},
    Share,
};
use bit::BitIndex;
use itertools::izip;
use log::debug;
use rand::Rng;
use std::{f64::consts::E, ops::Neg};

/// Number of AND triples needed for a A2B conversion.
pub const A2B_AND_TRIPLES: u64 = 13;

/// Fixed-point precision in bits.
const FIXED_POINT_PRECISION: u64 = 16;

/// Share `x` with given [`Share`] type.
pub fn x_to_shares(x: Share) -> (Share, Share) {
    let mut rng = rand::thread_rng();
    let share0: u64 = rng.gen();

    match x {
        Share::Arithmetic(x) => {
            let share1 = x.wrapping_sub(share0);
            (Share::Arithmetic(share0), Share::Arithmetic(share1))
        }
        Share::Binary(x) => {
            let share1 = x ^ share0;
            (Share::Binary(share0), Share::Binary(share1))
        }
    }
}

/// Reconstruct `x` from given [`Share`]s.
pub fn shares_to_x(shares: (Share, Share)) -> Result<u64> {
    match shares {
        (Share::Arithmetic(share0), Share::Arithmetic(share1)) => Ok(share0.wrapping_add(share1)),
        (Share::Binary(share0), Share::Binary(share1)) => Ok(share0 ^ share1),
        _ => Err(Error::DifferentShareTypes),
    }
}

pub trait EmbedFixedPoint {
    fn embed(self) -> Result<u64>;
}

impl EmbedFixedPoint for f64 {
    fn embed(self) -> Result<u64> {
        embed_fixed_point(self)
    }
}

pub trait ToFixedPoint {
    fn to_fixed_point(self) -> Result<f64>;
}

impl ToFixedPoint for u64 {
    fn to_fixed_point(self) -> Result<f64> {
        to_fixed_point(self)
    }
}

pub fn embed_fixed_point(fixed_point: f64) -> Result<u64> {
    if (fixed_point as i64) < (1 << (FIXED_POINT_PRECISION - 1))
        || (fixed_point as i64) >= -(1 << (FIXED_POINT_PRECISION - 1))
    {
        let scale = 1 << FIXED_POINT_PRECISION;
        Ok((fixed_point * scale as f64) as i64 as u64)
    } else {
        Err(Error::FixedPointEmbeddingError)
    }
}

pub fn to_fixed_point(embedded: u64) -> Result<f64> {
    let max = 1u64 << (2 * FIXED_POINT_PRECISION);
    if embedded > max && embedded < (u64::MAX - max) {
        Err(Error::FixedPointEmbeddingError)
    } else {
        let dividend = if embedded > (u64::MAX - max) {
            embedded.wrapping_sub(u64::MAX)
        } else {
            embedded
        };
        let scale = 1 << FIXED_POINT_PRECISION;
        let fixed_point = dividend as i64 as f64 / scale as f64;
        Ok(fixed_point)
    }
}

/// [`MPCExecutor`] handles MPC operations during execution.
#[derive(Debug)]
pub struct MPCExecutor<C: Channel, T: TripleProvider> {
    id: Id,
    ch: C,
    sender: OTSender,
    receiver: OTReceiver,
    triple_provider: T,
}

impl<C: Channel, T: TripleProvider> MPCExecutor<C, T> {
    /// Create new [`MPCExecutor`].
    pub fn new(id: Id, mut ch: C, triple_provider: T) -> Result<MPCExecutor<C, T>> {
        let sender = OTSender::new(&mut ch)?;
        let receiver = OTReceiver::new(&mut ch)?;
        Ok(MPCExecutor {
            id,
            ch,
            sender,
            receiver,
            triple_provider,
        })
    }

    /// Reveal the given [`Share`].
    pub fn reveal(&mut self, share: Share) -> Result<u64> {
        self.ch.send_share(share)?;
        let other = self.ch.recv_share()?;
        shares_to_x((share, other))
    }

    /// Reveal the two given [`Share`]s.
    pub fn reveal2(&mut self, shares: (Share, Share)) -> Result<(u64, u64)> {
        self.ch.send_share2(shares)?;
        let others = self.ch.recv_share2()?;
        Ok((
            shares_to_x((shares.0, others.0))?,
            shares_to_x((shares.1, others.1))?,
        ))
    }

    /// Reveal Vec of [`Share`]s.
    pub fn reveal_vec(&mut self, shares: Vec<Share>) -> Result<Vec<u64>> {
        self.ch.send_share_vec(&shares)?;
        let others = self.ch.recv_share_vec()?;
        shares.into_iter().zip(others).map(shares_to_x).collect()
    }

    /// Reveal the given [`Share`] for party with `id`.
    pub fn reveal_for(&mut self, share: Share, id: Id) -> Result<Option<u64>> {
        if self.id == id {
            let other = self.ch.recv_share()?;
            Ok(Some(shares_to_x((share, other))?))
        } else {
            self.ch.send_share(share)?;
            Ok(None)
        }
    }

    /// Add 2 binary shares using a optimized binary addition circuit.
    fn bin_add(&mut self, x: Integer, y: Integer) -> Result<Integer> {
        debug!("bin_add x = {x:?} y = {y:?}");
        let p = self.xor(x, y)?;
        let g = self.and(x, y)?;
        self.kogge_stone_inner(p, g)
    }

    /// Kogge stone adder.
    fn kogge_stone_inner(&mut self, p: Integer, g: Integer) -> Result<Integer> {
        let bitlen = 64;
        let d = 6; // log2 64
        let s_ = p.as_u64();
        let mut p = p.as_u64();
        let mut g = g.as_u64();
        for i in 0..d {
            let shift = 1 << i;
            let mut p_ = p;
            let mut g_ = g;
            let mask = (1u64 << (bitlen - shift)) - 1;
            p_ &= mask;
            g_ &= mask;
            let p_shift = Integer::Secret(Share::Binary(p >> shift));

            let r1 = self.and(p_shift, Integer::Secret(Share::Binary(g_)))?;
            let r2 = self.and(p_shift, Integer::Secret(Share::Binary(p_)))?;

            p = r2.as_u64() << shift;
            g ^= r1.as_u64() << shift;
        }
        g <<= 1;
        g ^= s_;
        Ok(Integer::Secret(Share::Binary(g)))
    }

    /// Convert a [`Secret`] from a [`Arithmetic`] share to a [`Binary`] share.
    ///
    /// [`Secret`]: Integer::Secret
    /// [`Arithmetic`]: Share::Arithmetic
    /// [`Binary`]: Share::Binary
    pub fn a2b(&mut self, x: Integer) -> Result<Integer> {
        debug!("a2b conversion src = {x:?}");
        if let Integer::Secret(Share::Arithmetic(share)) = x {
            // https://eprint.iacr.org/2018/403.pdf page 16
            let (a, b) = if self.id == Id::Party0 {
                (Share::Binary(share), Share::Binary(0))
            } else {
                (Share::Binary(0), Share::Binary(share))
            };

            self.bin_add(Integer::Secret(a), Integer::Secret(b))
        } else {
            Ok(x)
        }
    }

    /// Convert a [`Secret`] from a [`Binary`] share to a [`Arithmetic`] share.
    ///
    /// [`Secret`]: Integer::Secret
    /// [`Arithmetic`]: Share::Arithmetic
    /// [`Binary`]: Share::Binary
    pub fn b2a(&mut self, x: Integer) -> Result<Integer> {
        if let Integer::Secret(Share::Binary(x_b)) = x {
            let mut rng = rand::thread_rng();
            if self.id == Id::Party0 {
                let mut x_a = 0u64;
                let mut rs = Vec::new();
                for _ in 0..64 {
                    let tmp: u64 = rng.gen();
                    x_a = x_a.wrapping_add(tmp);
                    rs.push(tmp);
                }
                let mut inputs = Vec::new();
                for i in 0..64 {
                    let si0: u64 = ((1 - x_b.bit(i) as u64) * 2u64.pow(i as u32))
                        .wrapping_sub(*rs.get(i).unwrap());
                    let si1: u64 =
                        (x_b.bit(i) as u64 * 2u64.pow(i as u32)).wrapping_sub(*rs.get(i).unwrap());
                    inputs.push((Block::from(si0), Block::from(si1)));
                }
                self.sender.send(&mut self.ch, &inputs)?;
                x_a = !x_a;
                x_a += 1;
                debug!("id = {:?} x_a = {x_a}", self.id);
                Ok(Integer::Secret(Share::Arithmetic(x_a)))
            } else {
                let mut x_a = 0u64;
                let mut choices = Vec::new();
                for i in 0..64 {
                    choices.push(x_b.bit(i));
                }
                let res = self.receiver.receive(&mut self.ch, &choices)?;
                for e in res {
                    x_a = x_a.wrapping_add(e.try_into().unwrap());
                }
                x_a = !x_a;
                debug!("id = {:?} x_a = {x_a}", self.id);
                Ok(Integer::Secret(Share::Arithmetic(x_a)))
            }
        } else {
            Ok(x)
        }
    }

    pub fn add(&mut self, x: Integer, y: Integer) -> Result<Integer> {
        debug!("add x = {x:?} y = {y:?}");
        match (x, y) {
            (Integer::Public(x), Integer::Public(y)) => Ok(Integer::Public(x.wrapping_add(y))),
            (Integer::Secret(Share::Arithmetic(x)), Integer::Secret(Share::Arithmetic(y))) => {
                Ok(Integer::Secret(Share::Arithmetic(x.wrapping_add(y))))
            }
            (Integer::Secret(Share::Arithmetic(x)), Integer::Public(y)) => {
                if self.id == Id::Party0 {
                    Ok(Integer::Secret(Share::Arithmetic(x.wrapping_add(y))))
                } else {
                    Ok(Integer::Secret(Share::Arithmetic(x)))
                }
            }
            (Integer::Public(x), Integer::Secret(Share::Arithmetic(y))) => {
                if self.id == Id::Party0 {
                    Ok(Integer::Secret(Share::Arithmetic(x.wrapping_add(y))))
                } else {
                    Ok(Integer::Secret(Share::Arithmetic(0u64.wrapping_add(y))))
                }
            }
            _ => {
                let x = self.b2a(x)?;
                let y = self.b2a(y)?;
                self.add(x, y)
            }
        }
    }

    pub fn addi(&mut self, x: Integer, imm: i32) -> Result<Integer> {
        debug!("addi x = {x:?} imm = {imm}");
        self.add(x, Integer::Public(imm as u64))
    }

    pub fn fadd(&mut self, x: Float, y: Float) -> Result<Float> {
        debug!("fadd x = {x:?} y = {y:?}");
        match (x, y) {
            (Float::Public(x), Float::Public(y)) => Ok(Float::Public(x + y)),
            (Float::Secret(x), Float::Secret(y)) => Ok(Float::Secret(x.wrapping_add(y))),
            (Float::Secret(x), Float::Public(y)) => {
                if self.id == Id::Party0 {
                    Ok(Float::Secret(x.wrapping_add(y.embed()?)))
                } else {
                    Ok(Float::Secret(x))
                }
            }
            (Float::Public(x), Float::Secret(y)) => {
                if self.id == Id::Party0 {
                    Ok(Float::Secret(x.embed()?.wrapping_add(y)))
                } else {
                    Ok(Float::Secret(0u64.wrapping_add(y)))
                }
            }
        }
    }

    pub fn sub(&mut self, x: Integer, y: Integer) -> Result<Integer> {
        debug!("sub x = {x:?} y = {y:?}");
        match (x, y) {
            (Integer::Public(x), Integer::Public(y)) => Ok(Integer::Public(x.wrapping_sub(y))),
            (Integer::Secret(Share::Arithmetic(x)), Integer::Secret(Share::Arithmetic(y))) => {
                Ok(Integer::Secret(Share::Arithmetic(x.wrapping_sub(y))))
            }
            (Integer::Secret(Share::Arithmetic(x)), Integer::Public(y)) => {
                if self.id == Id::Party0 {
                    Ok(Integer::Secret(Share::Arithmetic(x.wrapping_sub(y))))
                } else {
                    Ok(Integer::Secret(Share::Arithmetic(x)))
                }
            }
            (Integer::Public(x), Integer::Secret(Share::Arithmetic(y))) => {
                if self.id == Id::Party0 {
                    Ok(Integer::Secret(Share::Arithmetic(x.wrapping_sub(y))))
                } else {
                    Ok(Integer::Secret(Share::Arithmetic(0u64.wrapping_sub(y))))
                }
            }
            _ => {
                let x = self.b2a(x)?;
                let y = self.b2a(y)?;
                self.sub(x, y)
            }
        }
    }

    pub fn fsub(&mut self, x: Float, y: Float) -> Result<Float> {
        debug!("fsub x = {x:?} y = {y:?}");
        match (x, y) {
            (Float::Public(x), Float::Public(y)) => Ok(Float::Public(x - y)),
            (Float::Secret(x), Float::Secret(y)) => Ok(Float::Secret(x.wrapping_sub(y))),
            (Float::Secret(x), Float::Public(y)) => {
                if self.id == Id::Party0 {
                    Ok(Float::Secret(x.wrapping_sub(y.embed()?)))
                } else {
                    Ok(Float::Secret(x))
                }
            }
            (Float::Public(x), Float::Secret(y)) => {
                if self.id == Id::Party0 {
                    Ok(Float::Secret(x.embed()?.wrapping_sub(y)))
                } else {
                    Ok(Float::Secret(0u64.wrapping_sub(y)))
                }
            }
        }
    }

    pub fn mul(&mut self, x: Integer, y: Integer) -> Result<Integer> {
        debug!("mul x = {x:?} y = {y:?}");
        match (x, y) {
            (Integer::Public(x), Integer::Public(y)) => Ok(Integer::Public(x.wrapping_mul(y))),
            (Integer::Secret(Share::Arithmetic(x)), Integer::Secret(Share::Arithmetic(y))) => {
                let (a, b, c) = self
                    .triple_provider
                    .mul_triple()
                    .ok_or(Error::BeaverTripleError)?;
                let d_share = Share::Arithmetic(x.wrapping_sub(a));
                let e_share = Share::Arithmetic(y.wrapping_sub(b));

                let (d, e) = self.reveal2((d_share, e_share))?;

                if self.id == Id::Party0 {
                    Ok(Integer::Secret(Share::Arithmetic(
                        c.wrapping_add(d.wrapping_mul(y))
                            .wrapping_add(e.wrapping_mul(x))
                            .wrapping_sub(d.wrapping_mul(e)),
                    )))
                } else {
                    Ok(Integer::Secret(Share::Arithmetic(
                        c.wrapping_add(d.wrapping_mul(y))
                            .wrapping_add(e.wrapping_mul(x)),
                    )))
                }
            }
            (Integer::Secret(Share::Arithmetic(x)), Integer::Public(y))
            | (Integer::Public(x), Integer::Secret(Share::Arithmetic(y))) => {
                Ok(Integer::Secret(Share::Arithmetic(x.wrapping_mul(y))))
            }
            _ => {
                let x = self.b2a(x)?;
                let y = self.b2a(y)?;
                self.mul(x, y)
            }
        }
    }

    // https://eprint.iacr.org/2017/396.pdf
    // https://www.esat.kuleuven.be/cosic/publications/article-3675.pdf
    fn fmul_truncate(&mut self, x: Integer) -> Result<Float> {
        if self.id == Id::Party0 {
            Ok(Float::Secret(x.as_u64() >> FIXED_POINT_PRECISION))
        } else {
            let tmp = self.sub(Integer::Public(u64::MAX), x)?;
            let tmp = self.sub(
                Integer::Public(u64::MAX),
                Integer::Secret(Share::Arithmetic(tmp.as_u64() >> FIXED_POINT_PRECISION)),
            )?;
            Ok(Float::Secret(tmp.as_u64()))
        }
    }

    pub fn fmul(&mut self, x: Float, y: Float) -> Result<Float> {
        debug!("fmul x = {x:?} y = {y:?}");
        match (x, y) {
            (Float::Public(x), Float::Public(y)) => Ok(Float::Public(x * y)),
            (Float::Secret(x), Float::Secret(y)) => {
                let (a, b, c) = self
                    .triple_provider
                    .mul_triple()
                    .ok_or(Error::BeaverTripleError)?;
                let d_share = Share::Arithmetic(x.wrapping_sub(a));
                let e_share = Share::Arithmetic(y.wrapping_sub(b));

                let (d, e) = self.reveal2((d_share, e_share))?;

                let res = if self.id == Id::Party0 {
                    Integer::Secret(Share::Arithmetic(
                        c.wrapping_add(d.wrapping_mul(y))
                            .wrapping_add(e.wrapping_mul(x))
                            .wrapping_sub(d.wrapping_mul(e)),
                    ))
                } else {
                    Integer::Secret(Share::Arithmetic(
                        c.wrapping_add(d.wrapping_mul(y))
                            .wrapping_add(e.wrapping_mul(x)),
                    ))
                };
                self.fmul_truncate(res)
            }
            (Float::Secret(y), Float::Public(x)) | (Float::Public(x), Float::Secret(y)) => {
                let res = Integer::Secret(Share::Arithmetic(x.embed()?.wrapping_mul(y)));
                self.fmul_truncate(res)
            }
        }
    }

    pub fn vmul(&mut self, x: &[Integer], y: &[Integer]) -> Result<Vec<Integer>> {
        debug!("vmul x = {x:?} y = {y:?}");
        match (x, y) {
            ([Integer::Public(_), ..], [Integer::Public(_), ..]) => x
                .iter()
                .zip(y)
                .map(|(x, y)| {
                    Ok(Integer::Public(
                        x.as_public().ok_or(Error::UnexpectedValue)?
                            * y.as_public().ok_or(Error::UnexpectedValue)?,
                    ))
                })
                .collect::<Result<Vec<Integer>>>(),
            (
                [Integer::Secret(Share::Arithmetic(_)), ..],
                [Integer::Secret(Share::Arithmetic(_)), ..],
            ) => {
                let triples = (0..x.len())
                    .map(|_| {
                        self.triple_provider
                            .mul_triple()
                            .ok_or(Error::BeaverTripleError)
                    })
                    .collect::<Result<Vec<(u64, u64, u64)>>>()?;
                let d_shares = x
                    .iter()
                    .zip(triples.iter())
                    .map(|(x, (a, _, _))| Share::Arithmetic(x.as_u64().wrapping_sub(*a)))
                    .collect::<Vec<Share>>();
                let e_shares = y
                    .iter()
                    .zip(triples.iter())
                    .map(|(y, (_, b, _))| Share::Arithmetic(y.as_u64().wrapping_sub(*b)))
                    .collect::<Vec<Share>>();
                let ds = self.reveal_vec(d_shares)?;
                let es = self.reveal_vec(e_shares)?;

                if self.id == Id::Party0 {
                    Ok(izip!(x, y, ds, es, triples)
                        .map(|(x, y, d, e, (_, _, c))| {
                            Integer::Secret(Share::Arithmetic(
                                c.wrapping_add(d.wrapping_mul(y.as_u64()))
                                    .wrapping_add(e.wrapping_mul(x.as_u64()))
                                    .wrapping_sub(d.wrapping_mul(e)),
                            ))
                        })
                        .collect::<Vec<Integer>>())
                } else {
                    Ok(izip!(x, y, ds, es, triples)
                        .map(|(x, y, d, e, (_, _, c))| {
                            Integer::Secret(Share::Arithmetic(
                                c.wrapping_add(d.wrapping_mul(y.as_u64()))
                                    .wrapping_add(e.wrapping_mul(x.as_u64())),
                            ))
                        })
                        .collect::<Vec<Integer>>())
                }
            }
            ([Integer::Secret(Share::Arithmetic(_)), ..], [Integer::Public(_), ..])
            | ([Integer::Public(_), ..], [Integer::Secret(Share::Arithmetic(_)), ..]) => Ok(x
                .iter()
                .zip(y)
                .map(|(x, y)| {
                    Integer::Secret(Share::Arithmetic(x.as_u64().wrapping_mul(y.as_u64())))
                })
                .collect::<Vec<Integer>>()),

            _ => {
                let x = x
                    .iter()
                    .map(|e| self.b2a(*e))
                    .collect::<Result<Vec<Integer>>>()?;
                let y = y
                    .iter()
                    .map(|e| self.b2a(*e))
                    .collect::<Result<Vec<Integer>>>()?;
                self.vmul(&x, &y)
            }
        }
    }

    pub fn vfmul(&mut self, x: &[Float], y: &[Float]) -> Result<Vec<Float>> {
        debug!("vfmul x = {x:?} y = {y:?}");
        match (x, y) {
            ([Float::Public(_), ..], [Float::Public(_), ..]) => x
                .iter()
                .zip(y)
                .map(|(x, y)| {
                    Ok(Float::Public(
                        x.as_public().ok_or(Error::UnexpectedValue)? * y.as_public().unwrap(),
                    ))
                })
                .collect::<Result<Vec<Float>>>(),
            ([Float::Secret(_), ..], [Float::Secret(_), ..]) => {
                let triples = (0..x.len())
                    .map(|_| {
                        self.triple_provider
                            .mul_triple()
                            .ok_or(Error::BeaverTripleError)
                    })
                    .collect::<Result<Vec<(u64, u64, u64)>>>()?;
                let d_shares = x
                    .iter()
                    .zip(triples.iter())
                    .map(|(x, (a, _, _))| {
                        Ok(Share::Arithmetic(
                            x.as_secret()
                                .ok_or(Error::UnexpectedValue)?
                                .wrapping_sub(*a),
                        ))
                    })
                    .collect::<Result<Vec<Share>>>()?;
                let e_shares = y
                    .iter()
                    .zip(triples.iter())
                    .map(|(y, (_, b, _))| {
                        Ok(Share::Arithmetic(
                            y.as_secret()
                                .ok_or(Error::UnexpectedValue)?
                                .wrapping_sub(*b),
                        ))
                    })
                    .collect::<Result<Vec<Share>>>()?;
                let ds = self.reveal_vec(d_shares)?;
                let es = self.reveal_vec(e_shares)?;

                let res = if self.id == Id::Party0 {
                    izip!(x, y, ds, es, triples)
                        .map(|(x, y, d, e, (_, _, c))| {
                            Ok(Integer::Secret(Share::Arithmetic(
                                c.wrapping_add(
                                    d.wrapping_mul(y.as_secret().ok_or(Error::UnexpectedValue)?),
                                )
                                .wrapping_add(
                                    e.wrapping_mul(x.as_secret().ok_or(Error::UnexpectedValue)?),
                                )
                                .wrapping_sub(d.wrapping_mul(e)),
                            )))
                        })
                        .collect::<Result<Vec<Integer>>>()?
                } else {
                    izip!(x, y, ds, es, triples)
                        .map(|(x, y, d, e, (_, _, c))| {
                            Ok(Integer::Secret(Share::Arithmetic(
                                c.wrapping_add(
                                    d.wrapping_mul(y.as_secret().ok_or(Error::UnexpectedValue)?),
                                )
                                .wrapping_add(
                                    e.wrapping_mul(x.as_secret().ok_or(Error::UnexpectedValue)?),
                                ),
                            )))
                        })
                        .collect::<Result<Vec<Integer>>>()?
                };

                // truncate after mul
                res.into_iter()
                    .map(|e| self.fmul_truncate(e))
                    .collect::<Result<Vec<Float>>>()
            }
            (x @ [Float::Secret(_), ..], y @ [Float::Public(_), ..])
            | (y @ [Float::Public(_), ..], x @ [Float::Secret(_), ..]) => {
                let res = x
                    .iter()
                    .zip(y)
                    .map(|(x, y)| {
                        Ok(Integer::Secret(Share::Arithmetic(
                            x.as_secret().unwrap().wrapping_mul(
                                y.as_public().ok_or(Error::UnexpectedValue)?.embed()?,
                            ),
                        )))
                    })
                    .collect::<Result<Vec<Integer>>>()?;
                // truncate after mul
                res.into_iter()
                    .map(|e| self.fmul_truncate(e))
                    .collect::<Result<Vec<Float>>>()
            }
            _ => {
                panic!("vectors not of same length");
            }
        }
    }

    pub fn div(&mut self, x: Integer, y: Integer) -> Result<Integer> {
        debug!("div x = {x:?} y = {y:?}");
        match (x, y) {
            (Integer::Public(x), Integer::Public(y)) => {
                if y == 0 {
                    Err(Error::DivByZero)
                } else {
                    Ok(Integer::Public(x / y))
                }
            }
            (Integer::Secret(Share::Arithmetic(x)), Integer::Public(y)) => {
                if y == 0 {
                    Err(Error::DivByZero)
                } else {
                    // TODO wrap count
                    // https://github.com/facebookresearch/CrypTen/blob/main/crypten/mpc/primitives/beaver.py#L129
                    let tmp = Integer::Secret(Share::Arithmetic(x / y));
                    self.sub(tmp, Integer::Public(u64::MAX / y))
                }
            }
            _ => Err(Error::DivBySecretValue),
        }
    }

    pub fn fdiv(&mut self, x: Float, y: Float) -> Result<Float> {
        debug!("fdiv x = {x:?} y = {y:?}");
        match (x, y) {
            (Float::Public(x), Float::Public(y)) => {
                if y == 0.0 {
                    Err(Error::DivByZero)
                } else {
                    Ok(Float::Public(x / y))
                }
            }
            (Float::Secret(x), Float::Public(y)) => {
                let res = self.div(
                    Integer::Secret(Share::Arithmetic(
                        x.wrapping_mul(1u64 << FIXED_POINT_PRECISION),
                    )),
                    Integer::Public(y.embed()?),
                )?;
                Ok(Float::Secret(res.as_u64()))
            }
            _ => {
                let inv = self.finv(y)?;
                self.fmul(x, inv)
            }
        }
    }

    pub fn rem(&mut self, x: Integer, y: Integer) -> Result<Integer> {
        debug!("rem x = {x:?} y = {y:?}");
        match (x, y) {
            (Integer::Public(x), Integer::Public(y)) => Ok(Integer::Public(x % y)),
            (Integer::Secret(_), Integer::Public(_)) => {
                let div = self.div(x, y)?;
                let mul = self.mul(div, y)?;
                self.sub(x, mul)
            }
            _ => Err(Error::DivBySecretValue),
        }
    }

    pub fn xor(&mut self, x: Integer, y: Integer) -> Result<Integer> {
        debug!("xor x = {x:?} y = {y:?}");
        match (x, y) {
            (Integer::Public(x), Integer::Public(y)) => Ok(Integer::Public(x ^ y)),
            (Integer::Secret(Share::Binary(x)), Integer::Secret(Share::Binary(y))) => {
                Ok(Integer::Secret(Share::Binary(x ^ y)))
            }
            (Integer::Secret(Share::Binary(x)), Integer::Public(y))
            | (Integer::Public(y), Integer::Secret(Share::Binary(x))) => {
                if self.id == Id::Party0 {
                    Ok(Integer::Secret(Share::Binary(x ^ y)))
                } else {
                    Ok(Integer::Secret(Share::Binary(x)))
                }
            }
            _ => {
                let x = self.a2b(x)?;
                let y = self.a2b(y)?;
                self.xor(x, y)
            }
        }
    }

    pub fn xori(&mut self, x: Integer, imm: i32) -> Result<Integer> {
        debug!("xori x = {x:?} imm = {imm}");
        self.xor(x, Integer::Public(imm as u64))
    }

    pub fn and(&mut self, x: Integer, y: Integer) -> Result<Integer> {
        debug!("and x = {x:?} y = {y:?}");
        match (x, y) {
            (Integer::Public(x), Integer::Public(y)) => Ok(Integer::Public(x & y)),
            (Integer::Secret(Share::Binary(x)), Integer::Secret(Share::Binary(y))) => {
                let (a, b, c) = self
                    .triple_provider
                    .and_triple()
                    .ok_or(Error::BeaverTripleError)?;
                let d_share = Share::Binary(x ^ a);
                let e_share = Share::Binary(y ^ b);

                let (d, e) = self.reveal2((d_share, e_share))?;

                if self.id == Id::Party0 {
                    Ok(Integer::Secret(Share::Binary(
                        (d & y) ^ (e & x) ^ (e & d) ^ c,
                    )))
                } else {
                    Ok(Integer::Secret(Share::Binary((d & y) ^ (e & x) ^ c)))
                }
            }
            (Integer::Secret(Share::Binary(x)), Integer::Public(y))
            | (Integer::Public(x), Integer::Secret(Share::Binary(y))) => {
                Ok(Integer::Secret(Share::Binary(x & y)))
            }
            _ => {
                let x = self.a2b(x)?;
                let y = self.a2b(y)?;
                self.and(x, y)
            }
        }
    }

    pub fn andi(&mut self, x: Integer, imm: i32) -> Result<Integer> {
        debug!("andi x = {x:?} imm = {imm}");
        self.and(x, Integer::Public(imm as u64))
    }

    pub fn vand(&mut self, x: &[Integer], y: &[Integer]) -> Result<Vec<Integer>> {
        debug!("vand x = {x:?} y = {y:?}");
        match (x, y) {
            ([Integer::Public(_), ..], [Integer::Public(_), ..]) => x
                .iter()
                .zip(y)
                .map(|(x, y)| {
                    Ok(Integer::Public(
                        x.as_public().ok_or(Error::UnexpectedValue)?
                            & y.as_public().ok_or(Error::UnexpectedValue)?,
                    ))
                })
                .collect::<Result<Vec<Integer>>>(),
            ([Integer::Secret(Share::Binary(_)), ..], [Integer::Secret(Share::Binary(_)), ..]) => {
                let triples = (0..x.len())
                    .map(|_| {
                        self.triple_provider
                            .and_triple()
                            .ok_or(Error::BeaverTripleError)
                    })
                    .collect::<Result<Vec<(u64, u64, u64)>>>()?;
                let d_shares = x
                    .iter()
                    .zip(triples.iter())
                    .map(|(x, (a, _, _))| Share::Binary(x.as_u64() ^ *a))
                    .collect::<Vec<Share>>();
                let e_shares = y
                    .iter()
                    .zip(triples.iter())
                    .map(|(y, (_, b, _))| Share::Binary(y.as_u64() ^ *b))
                    .collect::<Vec<Share>>();
                let ds = self.reveal_vec(d_shares)?;
                let es = self.reveal_vec(e_shares)?;

                if self.id == Id::Party0 {
                    Ok(izip!(x, y, ds, es, triples)
                        .map(|(x, y, d, e, (_, _, c))| {
                            Integer::Secret(Share::Binary(
                                (d & y.as_u64()) ^ (e & x.as_u64()) ^ (e & d) ^ c,
                            ))
                        })
                        .collect::<Vec<Integer>>())
                } else {
                    Ok(izip!(x, y, ds, es, triples)
                        .map(|(x, y, d, e, (_, _, c))| {
                            Integer::Secret(Share::Binary((d & y.as_u64()) ^ (e & x.as_u64()) ^ c))
                        })
                        .collect::<Vec<Integer>>())
                }
            }
            ([Integer::Secret(Share::Binary(_)), ..], [Integer::Public(_), ..])
            | ([Integer::Public(_), ..], [Integer::Secret(Share::Binary(_)), ..]) => Ok(x
                .iter()
                .zip(y)
                .map(|(x, y)| Integer::Secret(Share::Binary(x.as_u64() & y.as_u64())))
                .collect::<Vec<Integer>>()),

            _ => {
                let x = x
                    .iter()
                    .map(|e| self.a2b(*e))
                    .collect::<Result<Vec<Integer>>>()?;
                let y = y
                    .iter()
                    .map(|e| self.a2b(*e))
                    .collect::<Result<Vec<Integer>>>()?;
                self.vand(&x, &y)
            }
        }
    }

    pub fn or(&mut self, x: Integer, y: Integer) -> Result<Integer> {
        debug!("or x = {x:?} y = {y:?}");
        match (x, y) {
            (Integer::Public(x), Integer::Public(y)) => Ok(Integer::Public(x | y)),
            (Integer::Secret(Share::Binary(_)), Integer::Secret(Share::Binary(_)))
            | (Integer::Secret(Share::Binary(_)), Integer::Public(_))
            | (Integer::Public(_), Integer::Secret(Share::Binary(_))) => {
                let res = self.and(x, y)?;
                let res = self.xor(res, x)?;
                self.xor(res, y)
            }
            _ => {
                let x = self.a2b(x)?;
                let y = self.a2b(y)?;
                self.or(x, y)
            }
        }
    }

    pub fn ori(&mut self, x: Integer, imm: i32) -> Result<Integer> {
        debug!("ori x = {x:?} imm = {imm}");
        self.or(x, Integer::Public(imm as u64))
    }

    pub fn lshift(&mut self, x: Integer, y: Integer) -> Result<Integer> {
        debug!("lshift x = {x:?} y = {y:?}");
        match (x, y) {
            (Integer::Public(x), Integer::Public(y)) => Ok(Integer::Public(x << y)),
            (Integer::Secret(Share::Binary(x)), Integer::Public(y)) => {
                Ok(Integer::Secret(Share::Binary(x << y)))
            }
            (Integer::Secret(Share::Arithmetic(x)), Integer::Public(y)) => {
                Ok(Integer::Secret(Share::Arithmetic(x << y)))
            }
            _ => Err(Error::ShiftBySecretValue),
        }
    }

    pub fn rshift(&mut self, x: Integer, y: Integer) -> Result<Integer> {
        debug!("rshift x = {x:?} y = {y:?}");
        match (x, y) {
            (Integer::Public(x), Integer::Public(y)) => Ok(Integer::Public(x >> y)),
            (Integer::Secret(Share::Binary(x)), Integer::Public(y)) => {
                Ok(Integer::Secret(Share::Binary(x >> y)))
            }
            (Integer::Secret(Share::Arithmetic(_)), Integer::Public(y)) => {
                let x = self.a2b(x)?;
                Ok(Integer::Secret(Share::Binary(x.as_u64() >> y)))
            }
            _ => Err(Error::ShiftBySecretValue),
        }
    }

    pub fn lt(&mut self, x: Integer, y: Integer) -> Result<Integer> {
        match (x, y) {
            (Integer::Public(x), Integer::Public(y)) => Ok(Integer::Public((x < y) as u64)),
            (Integer::Secret(Share::Arithmetic(_)), Integer::Secret(Share::Arithmetic(_)))
            | (Integer::Secret(Share::Arithmetic(_)), Integer::Public(_))
            | (Integer::Public(_), Integer::Secret(Share::Arithmetic(_))) => {
                let z_a = self.sub(x, y)?;
                // TODO b2a_single_bit
                // https://github.com/facebookresearch/CrypTen/blob/main/crypten/mpc/primitives/beaver.py#L193
                let z_b = self.a2b(z_a)?;
                self.rshift(z_b, Integer::Public(63))
            }
            _ => {
                let x = self.b2a(x)?;
                let y = self.b2a(y)?;
                self.lt(x, y)
            }
        }
    }

    pub fn gt(&mut self, x: Integer, y: Integer) -> Result<Integer> {
        debug!("gt x = {x:?} y = {y:?}");
        self.lt(y, x)
    }

    pub fn le(&mut self, x: Integer, y: Integer) -> Result<Integer> {
        debug!("le x = {x:?} y = {y:?}");
        let gt = self.gt(x, y)?;
        self.sub(Integer::Public(1), gt)
    }

    #[allow(dead_code)]
    pub fn ge(&mut self, x: Integer, y: Integer) -> Result<Integer> {
        debug!("ge x = {x:?} y = {y:?}");
        let lt = self.lt(x, y)?;
        self.sub(Integer::Public(1), lt)
    }

    pub fn eq(&mut self, x: Integer, y: Integer) -> Result<Integer> {
        debug!("eq x = {x:?} y = {y:?}");
        let le = self.le(x, y)?;
        let lt = self.lt(x, y)?;
        self.sub(le, lt)
    }

    pub fn neq(&mut self, x: Integer, y: Integer) -> Result<Integer> {
        debug!("neq x = {x:?} y = {y:?}");
        let eq = self.eq(x, y)?;
        self.sub(Integer::Public(1), eq)
    }

    pub fn blt(&mut self, x: Integer, y: Integer) -> Result<bool> {
        match self.lt(x, y)? {
            Integer::Secret(share) => Ok(self.reveal(share)? != 0),
            Integer::Public(lt) => Ok(lt != 0),
        }
    }

    pub fn bgt(&mut self, x: Integer, y: Integer) -> Result<bool> {
        debug!("gt x = {x:?} y = {y:?}");
        self.blt(y, x)
    }

    pub fn ble(&mut self, x: Integer, y: Integer) -> Result<bool> {
        debug!("le x = {x:?} y = {y:?}");
        let gt = self.bgt(x, y)?;
        Ok(!gt)
    }

    pub fn bge(&mut self, x: Integer, y: Integer) -> Result<bool> {
        debug!("ge x = {x:?} y = {y:?}");
        let lt = self.blt(x, y)?;
        Ok(!lt)
    }

    pub fn beq(&mut self, x: Integer, y: Integer) -> Result<bool> {
        debug!("eq x = {x:?} y = {y:?}");
        let le = self.ble(x, y)?;
        let lt = self.blt(x, y)?;
        Ok(le && !lt)
    }

    pub fn flt(&mut self, x: Float, y: Float) -> Result<Integer> {
        match (x, y) {
            (Float::Public(x), Float::Public(y)) => Ok(Integer::Public((x < y) as u64)),
            (Float::Secret(_), Float::Secret(_))
            | (Float::Secret(_), Float::Public(_))
            | (Float::Public(_), Float::Secret(_)) => {
                let z_a = self.fsub(x, y)?;
                let z_b = self.a2b(Integer::Secret(Share::Arithmetic(z_a.as_secret().unwrap())))?;
                self.rshift(z_b, Integer::Public(63))
            }
        }
    }

    pub fn fle(&mut self, x: Float, y: Float) -> Result<Integer> {
        debug!("fle x = {x:?} y = {y:?}");
        let gt = self.flt(y, x)?;
        self.sub(Integer::Public(1), gt)
    }

    pub fn feq(&mut self, x: Float, y: Float) -> Result<Integer> {
        debug!("feq x = {x:?} y = {y:?}");
        let le = self.fle(x, y)?;
        let lt = self.flt(x, y)?;
        self.sub(le, lt)
    }

    pub fn fmin(&mut self, x: Float, y: Float) -> Result<Float> {
        debug!("fmin x = {x:?} y = {y:?}");
        match (x, y) {
            (Float::Public(x), Float::Public(y)) => Ok(Float::Public(x.min(y))),
            _ => {
                let lt = self.flt(x, y)?;
                let tmp = self.fsub(x, y)?;
                let tmp = self.fmul_integer(tmp, lt)?;
                let max = self.fadd(tmp, y)?;
                Ok(max)
            }
        }
    }

    pub fn fmax(&mut self, x: Float, y: Float) -> Result<Float> {
        debug!("fmin x = {x:?} y = {y:?}");
        match (x, y) {
            (Float::Public(x), Float::Public(y)) => Ok(Float::Public(x.max(y))),
            _ => {
                let lt = self.flt(x, y)?;
                let tmp = self.fsub(y, x)?;
                let tmp = self.fmul_integer(tmp, lt)?;
                let max = self.fadd(tmp, x)?;
                Ok(max)
            }
        }
    }

    pub fn fexp(&mut self, x: Float) -> Result<Float> {
        debug!("fexp x = {x:?}");
        match x {
            Float::Public(x) => Ok(Float::Public(E.powf(x))),
            Float::Secret(_) => {
                const ITERS: usize = 8;
                let tmp = self.fdiv(x, Float::Public(2.0f64.powi(ITERS as i32)))?;
                let mut res = self.fadd(tmp, Float::Public(1.0))?;
                for _ in 0..ITERS {
                    res = self.fmul(res, res)?;
                }
                Ok(res)
            }
        }
    }

    // TODO fails if x is bigger than approx 0.12
    pub fn finv(&mut self, x: Float) -> Result<Float> {
        debug!("finv x = {x:?}");
        match x {
            Float::Public(x) => Ok(Float::Public(1.0 / x)),
            Float::Secret(_) => {
                const ITERS: usize = 10;
                // result = 3 * (1 - 2 * self).exp() + 0.003
                let tmp = self.fmul(x, Float::Public(2.0))?;
                let tmp = self.fsub(Float::Public(1.0), tmp)?;
                let tmp = self.fexp(tmp)?;
                let tmp = self.fmul(tmp, Float::Public(3.0))?;
                let mut y = self.fadd(tmp, Float::Public(0.003))?;

                for _ in 0..ITERS {
                    // result = 2 * result - result * result * self
                    let tmp = self.fmul(y, Float::Public(2.0))?;
                    let tmp1 = self.fmul(y, y)?;
                    let tmp1 = self.fmul(tmp1, x)?;
                    y = self.fsub(tmp, tmp1)?;
                }
                Ok(y)
            }
        }
    }

    pub fn fsqrt(&mut self, x: Float) -> Result<Float> {
        debug!("fsqrt x = {x:?}");
        match x {
            Float::Public(x) => Ok(Float::Public(x.sqrt())),
            Float::Secret(x) => {
                const ITERS: usize = 3;
                // https://github.com/facebookresearch/CrypTen/blob/main/crypten/common/functions/approximations.py
                let x2 = self.fdiv(Float::Secret(x), Float::Public(2.0))?;
                let three_halfs = Float::Public(1.5);
                let tmp = self.fadd(x2, Float::Public(0.2))?;
                let tmp = self.fmul(tmp, Float::Public(-1.0))?;
                let tmp = self.fexp(tmp)?;
                let tmp = self.fmul(tmp, Float::Public(2.2))?;
                let tmp = self.fadd(tmp, Float::Public(0.2))?;
                let tmp1 = self.fdiv(Float::Secret(x), Float::Public(1024.0))?;
                let mut y = self.fsub(tmp, tmp1)?;

                // https://en.wikipedia.org/wiki/Fast_inverse_square_root
                for _ in 0..ITERS {
                    let tmp = self.fmul(y, y)?;
                    let tmp = self.fmul(x2, tmp)?;
                    let tmp = self.fsub(three_halfs, tmp)?;
                    y = self.fmul(y, tmp)?;
                }
                // inv_sqrt * x
                let res = self.fmul(y, Float::Secret(x))?;
                Ok(res)
            }
        }
    }

    pub fn fsign(&mut self, x: Float) -> Result<Integer> {
        debug!("float_get_sign_bit x = {x:?}");
        let gtz = self.flt(Float::Public(0.0), x)?;
        let tmp = self.mul(gtz, Integer::Public(2))?;
        let sign = self.sub(tmp, Integer::Public(1))?;
        Ok(sign)
    }

    pub fn fabs(&mut self, x: Float) -> Result<Float> {
        debug!("fabs x = {x:?}");
        let sign = self.fsign(x)?;
        match x {
            Float::Public(x) => Ok(Float::Public(x.abs())),
            Float::Secret(x) => Ok(Float::Secret(
                self.mul(Integer::Secret(Share::Arithmetic(x)), sign)?
                    .as_u64(),
            )),
        }
    }

    pub fn fmul_integer(&mut self, x: Float, y: Integer) -> Result<Float> {
        debug!("fmul_integer x = {x:?} y = {y:?}");
        match x {
            Float::Public(x) => match y {
                Integer::Public(sign) => Ok(Float::Public(x * sign as i64 as f64)),
                Integer::Secret(_) => Ok(Float::Secret(
                    self.mul(y, Integer::Public(x.embed()?))?.as_u64(),
                )),
            },
            Float::Secret(x) => Ok(Float::Secret(
                self.mul(Integer::Secret(Share::Arithmetic(x)), y)?.as_u64(),
            )),
        }
    }

    pub fn fsgnj(&mut self, x: Float, y: Float) -> Result<Float> {
        debug!("fsignj x = {x:?} y = {y:?}");
        let sign_y = self.fsign(y)?;
        let abs_x = self.fabs(x)?;
        self.fmul_integer(abs_x, sign_y)
    }

    pub fn fsgnjn(&mut self, x: Float, y: Float) -> Result<Float> {
        debug!("fsignjn x = {x:?} y = {y:?}");
        let sign_y = self.fsign(y)?;
        let sign = self.sub(Integer::Public(0), sign_y)?;
        let abs_x = self.fabs(x)?;
        self.fmul_integer(abs_x, sign)
    }

    pub fn fsgnjx(&mut self, x: Float, y: Float) -> Result<Float> {
        debug!("fsignjx x = {x:?} y = {y:?}");
        let sign_y = self.fsign(y)?;
        let sign = self.sub(Integer::Public(0), sign_y)?;
        let abs_x = self.fabs(x)?;
        self.fmul_integer(abs_x, sign)
    }

    pub fn fcvtlud(&mut self, x: Float) -> Result<Integer> {
        debug!("fcvt d to lu x = {x:?}");
        match x {
            Float::Public(x) => Ok(Integer::Public(x as u64)),
            Float::Secret(x) => self.div(
                Integer::Secret(Share::Arithmetic(x)),
                Integer::Public(1u64 << FIXED_POINT_PRECISION),
            ),
        }
    }

    pub fn fcvtdlu(&mut self, x: Integer) -> Result<Float> {
        debug!("fcvt lu to d x = {x:?}");
        match x {
            Integer::Public(x) => Ok(Float::Public(x as f64)),
            Integer::Secret(_) => {
                let embedded = self.mul(x, Integer::Public(1u64 << FIXED_POINT_PRECISION))?;
                Ok(Float::Secret(embedded.as_u64()))
            }
        }
    }

    pub fn fneg(&mut self, x: Float) -> Result<Float> {
        match x {
            Float::Public(x) => Ok(Float::Public(x.neg())),
            Float::Secret(_) => self.fmul(x, Float::Public(-1.0)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::channel::ThreadChannel;
    use crate::party::Id;
    use crate::triple_provider::Triple;
    use crate::types::Value;
    use approx::assert_relative_eq;
    use bytes::Bytes;
    use std::{
        sync::mpsc::{self, Receiver, Sender},
        thread,
    };

    #[derive(Debug, Clone, Copy)]
    enum Output {
        Integer(u64),
        Float(f64),
    }

    impl From<u64> for Output {
        fn from(value: u64) -> Self {
            Output::Integer(value)
        }
    }

    impl From<f64> for Output {
        fn from(value: f64) -> Self {
            Output::Float(value)
        }
    }

    struct TestTripleProvider;

    impl TripleProvider for TestTripleProvider {
        fn mul_triple(&mut self) -> Option<Triple> {
            Some((0, 0, 0))
        }

        fn and_triple(&mut self) -> Option<Triple> {
            Some((0, 0, 0))
        }
    }

    fn create_channels() -> (ThreadChannel, ThreadChannel) {
        let (tx0, rx0): (Sender<Bytes>, Receiver<Bytes>) = mpsc::channel();
        let (tx1, rx1): (Sender<Bytes>, Receiver<Bytes>) = mpsc::channel();
        let ch0 = ThreadChannel::new(tx0, rx1);
        let ch1 = ThreadChannel::new(tx1, rx0);
        (ch0, ch1)
    }

    fn inputs(x: Value) -> (Value, Value) {
        match x {
            Value::Integer(Integer::Secret(x)) => {
                let (x0, x1) = x_to_shares(x);
                (Integer::Secret(x0).into(), Integer::Secret(x1).into())
            }
            Value::Integer(Integer::Public(_)) => (x, x),
            Value::Float(Float::Secret(x)) => {
                let (x0, x1) = x_to_shares(Share::Arithmetic(x));
                (
                    Float::Secret(x0.into()).into(),
                    Float::Secret(x1.into()).into(),
                )
            }
            Value::Float(Float::Public(_)) => (x, x),
        }
    }

    fn verify(
        res: Value,
        expected: Output,
        executor: &mut MPCExecutor<ThreadChannel, TestTripleProvider>,
    ) {
        match res {
            Value::Integer(integer) => {
                let res = match integer {
                    Integer::Secret(share) => executor.reveal(share).unwrap(),
                    Integer::Public(res) => res,
                };
                match expected {
                    Output::Integer(expected) => assert_eq!(res, expected),
                    _ => panic!("expected integer"),
                }
            }
            Value::Float(float) => {
                let res = match float {
                    Float::Secret(embedded) => {
                        to_fixed_point(executor.reveal(Share::Arithmetic(embedded)).unwrap())
                            .unwrap()
                    }
                    Float::Public(res) => res,
                };
                match expected {
                    Output::Float(expected) => assert_relative_eq!(res, expected, epsilon = 10e-3),
                    _ => panic!("expected float"),
                }
            }
        }
    }

    macro_rules! test {
        ($f:expr, $x:expr, $y:expr, $expected:expr) => {{
            let run = |id: Id, ch: ThreadChannel, x: Value, y: Value, expected: Output| {
                let mut executor = MPCExecutor::new(id, ch, TestTripleProvider).unwrap();
                let value = $f(&mut executor, x.try_into().unwrap(), y.try_into().unwrap())
                    .unwrap()
                    .into();
                verify(value, expected, &mut executor);
            };
            let (ch0, ch1) = create_channels();
            let (x0, x1) = inputs($x.into());
            let (y0, y1) = inputs($y.into());
            let party0 = thread::spawn(move || run(Id::Party0, ch0, x0, y0, $expected));
            let party1 = thread::spawn(move || run(Id::Party1, ch1, x1, y1, $expected));
            party0.join().unwrap();
            party1.join().unwrap();
        }};
        ($f:expr, $x:expr, $expected:expr) => {{
            let run = |id: Id, ch: ThreadChannel, x: Value, expected: Output| {
                let mut executor = MPCExecutor::new(id, ch, TestTripleProvider).unwrap();
                let value = $f(&mut executor, x.try_into().unwrap()).unwrap().into();
                verify(value, expected, &mut executor);
            };
            let (ch0, ch1) = create_channels();
            let (x0, x1) = inputs($x.into());
            let party0 = thread::spawn(move || run(Id::Party0, ch0, x0, $expected));
            let party1 = thread::spawn(move || run(Id::Party1, ch1, x1, $expected));
            party0.join().unwrap();
            party1.join().unwrap();
        }};
    }

    macro_rules! test_vec {
        ($f:expr, $x:expr, $y:expr, $expected:expr) => {{
            let run = |id: Id, ch: ThreadChannel, x: &[Value], y: &[Value], expected: &[Output]| {
                let mut executor = MPCExecutor::new(id, ch, TestTripleProvider).unwrap();
                let values = $f(
                    &mut executor,
                    &x.iter()
                        .map(|x| (*x).try_into())
                        .collect::<Result<Vec<_>>>()
                        .unwrap(),
                    &y.iter()
                        .map(|y| (*y).try_into())
                        .collect::<Result<Vec<_>>>()
                        .unwrap(),
                )
                .unwrap();
                for (value, expected) in values.into_iter().zip(expected) {
                    verify(value.into(), *expected, &mut executor);
                }
            };

            let (ch0, ch1) = create_channels();
            let (x0, x1): (Vec<Value>, Vec<Value>) = $x.iter().map(|x| inputs((*x).into())).unzip();
            let (y0, y1): (Vec<Value>, Vec<Value>) = $y.iter().map(|y| inputs((*y).into())).unzip();
            let party0 = thread::spawn(move || run(Id::Party0, ch0, &x0, &y0, &$expected));
            let party1 = thread::spawn(move || run(Id::Party1, ch1, &x1, &y1, &$expected));
            party0.join().unwrap();
            party1.join().unwrap();
        }};
    }

    #[test]
    fn arithmetic_share() {
        let shares = x_to_shares(Share::Arithmetic(42));
        assert_eq!(shares_to_x(shares).unwrap(), 42);
    }

    #[test]
    fn binary_share() {
        let shares = x_to_shares(Share::Binary(42));
        assert_eq!(shares_to_x(shares).unwrap(), 42);
    }

    #[test]
    fn test_fixed_point() {
        let embedded = 0.0.embed().unwrap();
        let shares = x_to_shares(Share::Arithmetic(embedded));
        let embedded = shares_to_x(shares).unwrap();
        let fp = embedded.to_fixed_point().unwrap();
        assert_eq!(fp, 0.0)
    }

    #[test]
    fn bin_add() {
        let x = Integer::Secret(Share::Binary(3));
        let y = Integer::Secret(Share::Binary(2));
        test!(MPCExecutor::bin_add, x, y, 5.into())
    }

    #[test]
    fn add_public_public() {
        let x = Integer::Public(3);
        let y = Integer::Public(2);
        test!(MPCExecutor::add, x, y, 5.into())
    }

    #[test]
    fn add_secret_public() {
        let x = Integer::Secret(Share::Arithmetic(3));
        let y = Integer::Public(2);
        test!(MPCExecutor::add, x, y, 5.into());
    }

    #[test]
    fn add_secret_secret() {
        let x = Integer::Secret(Share::Arithmetic(3));
        let y = Integer::Secret(Share::Arithmetic(2));
        test!(MPCExecutor::add, x, y, 5.into());
    }

    #[test]
    fn sub_public_public() {
        let x = Integer::Public(5);
        let y = Integer::Public(2);
        test!(MPCExecutor::sub, x, y, 3.into());
    }

    #[test]
    fn sub_secret_public() {
        let x = Integer::Secret(Share::Arithmetic(5));
        let y = Integer::Public(2);
        test!(MPCExecutor::sub, x, y, 3.into());
    }

    #[test]
    fn sub_secret_secret() {
        let x = Integer::Secret(Share::Arithmetic(5));
        let y = Integer::Secret(Share::Arithmetic(2));
        test!(MPCExecutor::sub, x, y, 3.into());
    }

    #[test]
    fn mul_public_public() {
        let x = Integer::Public(3);
        let y = Integer::Public(2);
        test!(MPCExecutor::mul, x, y, 6.into());
    }

    #[test]
    fn mul_secret_public() {
        let x = Integer::Secret(Share::Arithmetic(3));
        let y = Integer::Public(2);
        test!(MPCExecutor::mul, x, y, 6.into());
    }

    #[test]
    fn mul_secret_secret() {
        let x = Integer::Secret(Share::Arithmetic(3));
        let y = Integer::Secret(Share::Arithmetic(2));
        test!(MPCExecutor::mul, x, y, 6.into());
    }

    #[test]
    fn div_public_public() {
        let x = Integer::Public(8);
        let y = Integer::Public(2);
        test!(MPCExecutor::div, x, y, 4.into());
    }

    #[ignore = "can be off by 1"]
    #[test]
    fn div_secret_public() {
        let x = Integer::Secret(Share::Arithmetic(8));
        let y = Integer::Public(2);
        test!(MPCExecutor::div, x, y, 4.into());
        let x = Integer::Secret(Share::Arithmetic(9));
        let y = Integer::Public(3);
        test!(MPCExecutor::div, x, y, 3.into());
    }

    #[test]
    fn rem_public_public() {
        let x = Integer::Public(8);
        let y = Integer::Public(2);
        test!(MPCExecutor::rem, x, y, 0.into());
    }

    #[ignore = "will fail if div is off by 1"]
    #[test]
    fn rem_secret_public() {
        let x = Integer::Secret(Share::Arithmetic(8));
        let y = Integer::Public(2);
        test!(MPCExecutor::rem, x, y, 0.into());
    }

    #[test]
    fn xor_public_public() {
        let x = Integer::Public(0b1111);
        let y = Integer::Public(0b0110);
        test!(MPCExecutor::xor, x, y, 0b1001.into());
    }

    #[test]
    fn xor_secret_public() {
        let x = Integer::Secret(Share::Binary(0b1111));
        let y = Integer::Public(0b0110);
        test!(MPCExecutor::xor, x, y, 0b1001.into());
    }

    #[test]
    fn xor_secret_secret() {
        let x = Integer::Secret(Share::Binary(0b1111));
        let y = Integer::Secret(Share::Binary(0b0110));
        test!(MPCExecutor::xor, x, y, 0b1001.into());
    }

    #[test]
    fn and_public_public() {
        let x = Integer::Public(0b1111);
        let y = Integer::Public(0b0110);
        test!(MPCExecutor::and, x, y, 0b0110.into());
    }

    #[test]
    fn and_secret_public() {
        let x = Integer::Secret(Share::Binary(0b1111));
        let y = Integer::Public(0b0110);
        test!(MPCExecutor::and, x, y, 0b0110.into());
    }

    #[test]
    fn and_secret_secret() {
        let x = Integer::Secret(Share::Binary(0b1111));
        let y = Integer::Secret(Share::Binary(0b0110));
        test!(MPCExecutor::and, x, y, 0b0110.into());
    }

    #[test]
    fn or_public_public() {
        let x = Integer::Public(0b0100);
        let y = Integer::Public(0b0110);
        test!(MPCExecutor::or, x, y, 0b0110.into());
    }

    #[test]
    fn or_secret_public() {
        let x = Integer::Secret(Share::Binary(0b0100));
        let y = Integer::Public(0b0110);
        test!(MPCExecutor::or, x, y, 0b0110.into());
    }

    #[test]
    fn or_secret_secret() {
        let x = Integer::Secret(Share::Binary(0b0100));
        let y = Integer::Secret(Share::Binary(0b0110));
        test!(MPCExecutor::or, x, y, 0b0110.into());
    }

    #[test]
    fn lshift_public_public() {
        let x = Integer::Public(1);
        let y = Integer::Public(7);
        test!(MPCExecutor::lshift, x, y, 128.into());
    }

    #[test]
    fn lshift_secret_public() {
        let x = Integer::Secret(Share::Binary(1));
        let y = Integer::Public(7);
        test!(MPCExecutor::lshift, x, y, 128.into());
        let x = Integer::Secret(Share::Arithmetic(1));
        let y = Integer::Public(7);
        test!(MPCExecutor::lshift, x, y, 128.into());
    }

    #[test]
    fn rshift_public_public() {
        let x = Integer::Public(256);
        let y = Integer::Public(1);
        test!(MPCExecutor::rshift, x, y, 128.into());
    }

    #[test]
    fn rshift_secret_public() {
        let x = Integer::Secret(Share::Binary(256));
        let y = Integer::Public(1);
        test!(MPCExecutor::rshift, x, y, 128.into());
        let x = Integer::Secret(Share::Arithmetic(256));
        let y = Integer::Public(1);
        test!(MPCExecutor::rshift, x, y, 128.into());
    }

    #[test]
    fn lt_public_public() {
        let x = Integer::Public(3);
        let y = Integer::Public(5);
        test!(MPCExecutor::lt, x, y, 1.into());
        test!(MPCExecutor::lt, y, x, 0.into());
    }

    #[test]
    fn lt_public_secret() {
        let x = Integer::Public(3);
        let y = Integer::Secret(Share::Arithmetic(5));
        test!(MPCExecutor::lt, x, y, 1.into());
        test!(MPCExecutor::lt, y, x, 0.into());
    }

    #[test]
    fn lt_secret_secret() {
        let x = Integer::Secret(Share::Arithmetic(3));
        let y = Integer::Secret(Share::Arithmetic(5));
        test!(MPCExecutor::lt, x, y, 1.into());
        test!(MPCExecutor::lt, y, x, 0.into());
    }

    #[test]
    fn gt_public_public() {
        let x = Integer::Public(3);
        let y = Integer::Public(5);
        test!(MPCExecutor::gt, x, y, 0.into());
        test!(MPCExecutor::gt, y, x, 1.into());
    }

    #[test]
    fn gt_public_secret() {
        let x = Integer::Public(3);
        let y = Integer::Secret(Share::Arithmetic(5));
        test!(MPCExecutor::gt, x, y, 0.into());
        test!(MPCExecutor::gt, y, x, 1.into());
    }

    #[test]
    fn gt_secret_secret() {
        let x = Integer::Secret(Share::Arithmetic(3));
        let y = Integer::Secret(Share::Arithmetic(5));
        test!(MPCExecutor::gt, x, y, 0.into());
        test!(MPCExecutor::gt, y, x, 1.into());
    }

    #[test]
    fn le_public_public() {
        let x = Integer::Public(3);
        let y = Integer::Public(5);
        test!(MPCExecutor::le, x, y, 1.into());
        test!(MPCExecutor::le, y, x, 0.into());
        let x = Integer::Public(5);
        let y = Integer::Public(5);
        test!(MPCExecutor::le, x, y, 1.into());
    }

    #[test]
    fn le_public_secret() {
        let x = Integer::Public(3);
        let y = Integer::Secret(Share::Arithmetic(5));
        test!(MPCExecutor::le, x, y, 1.into());
        test!(MPCExecutor::le, y, x, 0.into());
        let x = Integer::Public(5);
        let y = Integer::Secret(Share::Arithmetic(5));
        test!(MPCExecutor::le, x, y, 1.into());
    }

    #[test]
    fn le_secret_secret() {
        let x = Integer::Secret(Share::Arithmetic(3));
        let y = Integer::Secret(Share::Arithmetic(5));
        test!(MPCExecutor::le, x, y, 1.into());
        test!(MPCExecutor::le, y, x, 0.into());
        let x = Integer::Secret(Share::Arithmetic(5));
        let y = Integer::Secret(Share::Arithmetic(5));
        test!(MPCExecutor::le, x, y, 1.into());
    }

    #[test]
    fn ge_public_public() {
        let x = Integer::Public(3);
        let y = Integer::Public(5);
        test!(MPCExecutor::ge, x, y, 0.into());
        test!(MPCExecutor::ge, y, x, 1.into());
        let x = Integer::Public(5);
        let y = Integer::Public(5);
        test!(MPCExecutor::ge, x, y, 1.into());
    }

    #[test]
    fn ge_public_secret() {
        let x = Integer::Public(3);
        let y = Integer::Secret(Share::Arithmetic(5));
        test!(MPCExecutor::ge, x, y, 0.into());
        test!(MPCExecutor::ge, y, x, 1.into());
        let x = Integer::Public(5);
        let y = Integer::Secret(Share::Arithmetic(5));
        test!(MPCExecutor::ge, x, y, 1.into());
    }

    #[test]
    fn ge_secret_secret() {
        let x = Integer::Secret(Share::Arithmetic(3));
        let y = Integer::Secret(Share::Arithmetic(5));
        test!(MPCExecutor::ge, x, y, 0.into());
        test!(MPCExecutor::ge, y, x, 1.into());
        let x = Integer::Secret(Share::Arithmetic(5));
        let y = Integer::Secret(Share::Arithmetic(5));
        test!(MPCExecutor::ge, x, y, 1.into());
    }

    #[test]
    fn eq_public_public() {
        let x = Integer::Public(3);
        let y = Integer::Public(5);
        test!(MPCExecutor::eq, x, y, 0.into());
        let x = Integer::Public(5);
        let y = Integer::Public(5);
        test!(MPCExecutor::eq, x, y, 1.into());
    }

    #[test]
    fn eq_public_secret() {
        let x = Integer::Public(3);
        let y = Integer::Secret(Share::Arithmetic(5));
        test!(MPCExecutor::eq, x, y, 0.into());
        let x = Integer::Public(5);
        let y = Integer::Secret(Share::Arithmetic(5));
        test!(MPCExecutor::eq, x, y, 1.into());
    }

    #[test]
    fn eq_secret_secret() {
        let x = Integer::Secret(Share::Arithmetic(3));
        let y = Integer::Secret(Share::Arithmetic(5));
        test!(MPCExecutor::eq, x, y, 0.into());
        let x = Integer::Secret(Share::Arithmetic(5));
        let y = Integer::Secret(Share::Arithmetic(5));
        test!(MPCExecutor::eq, x, y, 1.into());
    }

    #[test]
    fn neq_public_public() {
        let x = Integer::Public(3);
        let y = Integer::Public(5);
        test!(MPCExecutor::neq, x, y, 1.into());
        let x = Integer::Public(5);
        let y = Integer::Public(5);
        test!(MPCExecutor::neq, x, y, 0.into());
    }

    #[test]
    fn neq_public_secret() {
        let x = Integer::Public(3);
        let y = Integer::Secret(Share::Arithmetic(5));
        test!(MPCExecutor::neq, x, y, 1.into());
        let x = Integer::Public(5);
        let y = Integer::Secret(Share::Arithmetic(5));
        test!(MPCExecutor::neq, x, y, 0.into());
    }

    #[test]
    fn neq_secret_secret() {
        let x = Integer::Secret(Share::Arithmetic(3));
        let y = Integer::Secret(Share::Arithmetic(5));
        test!(MPCExecutor::neq, x, y, 1.into());
        let x = Integer::Secret(Share::Arithmetic(5));
        let y = Integer::Secret(Share::Arithmetic(5));
        test!(MPCExecutor::neq, x, y, 0.into());
    }

    #[test]
    fn a2b() {
        let x = Integer::Secret(Share::Arithmetic(42));
        test!(MPCExecutor::a2b, x, 42.into())
    }

    #[test]
    fn b2a() {
        let x = Integer::Secret(Share::Binary(42));
        test!(MPCExecutor::b2a, x, 42.into())
    }

    #[test]
    fn fadd_public_public() {
        let x = Float::Public(1.5);
        let y = Float::Public(0.5);
        test!(MPCExecutor::fadd, x, y, 2.0.into());
    }

    #[test]
    fn fadd_secret_public() {
        let x = Float::Secret(1.5.embed().unwrap());
        let y = Float::Public(0.5);
        test!(MPCExecutor::fadd, x, y, 2.0.into());
    }

    #[test]
    fn fadd_secret_secret() {
        let x = Float::Secret(1.5.embed().unwrap());
        let y = Float::Secret(0.5.embed().unwrap());
        test!(MPCExecutor::fadd, x, y, 2.0.into());
        let x = Float::Secret(1.5.embed().unwrap());
        let y = Float::Secret(0.0.embed().unwrap());
        test!(MPCExecutor::fadd, x, y, 1.5.into());
    }

    #[test]
    fn fsub_public_public() {
        let x = Float::Public(1.5);
        let y = Float::Public(0.5);
        test!(MPCExecutor::fsub, x, y, 1.0.into());
    }

    #[test]
    fn fsub_secret_public() {
        let x = Float::Secret(1.5.embed().unwrap());
        let y = Float::Public(0.5);
        test!(MPCExecutor::fsub, x, y, 1.0.into());
    }

    #[test]
    fn fsub_secret_secret() {
        let x = Float::Secret(1.5.embed().unwrap());
        let y = Float::Secret(0.5.embed().unwrap());
        test!(MPCExecutor::fsub, x, y, 1.0.into());
    }

    #[test]
    fn fmul_public_public() {
        let x = Float::Public(1.5);
        let y = Float::Public(0.5);
        test!(MPCExecutor::fmul, x, y, 0.75.into());
    }

    #[test]
    fn fmul_secret_public() {
        let x = Float::Secret(1.5.embed().unwrap());
        let y = Float::Public(0.5);
        test!(MPCExecutor::fmul, x, y, 0.75.into());
    }

    #[test]
    fn fmul_secret_secret() {
        let x = Float::Secret(1.5.embed().unwrap());
        let y = Float::Secret(0.0.embed().unwrap());
        test!(MPCExecutor::fmul, x, y, 0.0.into());
        let x = Float::Secret(1.5.embed().unwrap());
        let y = Float::Secret(0.5.embed().unwrap());
        test!(MPCExecutor::fmul, x, y, 0.75.into());
        let x = Float::Secret(1.5.embed().unwrap());
        let y = Float::Secret((-0.5).embed().unwrap());
        test!(MPCExecutor::fmul, x, y, (-0.75).into());
        let x = Float::Secret(0.0.embed().unwrap());
        let y = Float::Secret(0.0.embed().unwrap());
        test!(MPCExecutor::fmul, x, y, 0.0.into());
    }

    #[test]
    fn fdiv_public_public() {
        let x = Float::Public(7.0);
        let y = Float::Public(2.0);
        test!(MPCExecutor::fdiv, x, y, 3.5.into());
    }

    #[test]
    fn fdiv_secret_public() {
        let x = Float::Secret(7.0.embed().unwrap());
        let y = Float::Public(2.0);
        test!(MPCExecutor::fdiv, x, y, 3.5.into());
    }

    #[test]
    fn fdiv_secret_secret() {
        let x = Float::Secret(7.0.embed().unwrap());
        let y = Float::Secret(2.0.embed().unwrap());
        test!(MPCExecutor::fdiv, x, y, 3.5.into());
    }

    #[test]
    fn flt_secret_secret() {
        let x = Float::Secret(7.0.embed().unwrap());
        let y = Float::Secret(2.0.embed().unwrap());
        test!(MPCExecutor::flt, x, y, 0.into());
        test!(MPCExecutor::flt, y, x, 1.into());
    }

    #[test]
    fn fmin_public_public() {
        let x = Float::Public(1.5);
        let y = Float::Public(0.5);
        test!(MPCExecutor::fmin, x, y, 0.5.into());
    }

    #[test]
    fn fmin_secret_public() {
        let x = Float::Secret(1.5.embed().unwrap());
        let y = Float::Public(0.5);
        test!(MPCExecutor::fmin, x, y, 0.5.into());
    }

    #[test]
    fn fmin_secret_secret() {
        let x = Float::Secret(1.5.embed().unwrap());
        let y = Float::Secret(0.5.embed().unwrap());
        test!(MPCExecutor::fmin, x, y, 0.5.into());
    }

    #[test]
    fn fmax_public_public() {
        let x = Float::Public(1.5);
        let y = Float::Public(0.5);
        test!(MPCExecutor::fmax, x, y, 1.5.into());
    }

    #[test]
    fn fmax_secret_public() {
        let x = Float::Secret(1.5.embed().unwrap());
        let y = Float::Public(0.5);
        test!(MPCExecutor::fmax, x, y, 1.5.into());
    }

    #[test]
    fn fmax_secret_secret() {
        let x = Float::Secret(1.5.embed().unwrap());
        let y = Float::Secret(0.5.embed().unwrap());
        test!(MPCExecutor::fmax, x, y, 1.5.into());
        let x = Float::Secret(1.5.embed().unwrap());
        let y = Float::Secret(0.0.embed().unwrap());
        test!(MPCExecutor::fmax, x, y, 1.5.into());
        let x = Float::Secret((-1.5).embed().unwrap());
        let y = Float::Secret(0.0.embed().unwrap());
        test!(MPCExecutor::fmax, x, y, 0.0.into());
    }

    #[test]
    fn fsgnj_public_public() {
        let x = Float::Public(1.5);
        let y = Float::Public(-1.0);
        test!(MPCExecutor::fsgnj, x, y, (-1.5).into());
    }

    #[test]
    fn fsgnj_secret_public() {
        let x = Float::Secret(1.5.embed().unwrap());
        let y = Float::Public(-1.0);
        test!(MPCExecutor::fsgnj, x, y, (-1.5).into());
    }

    #[test]
    fn fsgnj_secret_secret() {
        let x = Float::Secret(1.5.embed().unwrap());
        let y = Float::Secret((-0.5).embed().unwrap());
        test!(MPCExecutor::fsgnj, x, y, (-1.5).into());
    }

    #[test]
    fn fsgnjn_public_public() {
        let x = Float::Public(1.5);
        let y = Float::Public(-1.0);
        test!(MPCExecutor::fsgnjn, x, y, 1.5.into());
    }

    #[test]
    fn fsgnjn_secret_public() {
        let x = Float::Secret(1.5.embed().unwrap());
        let y = Float::Public(-1.0);
        test!(MPCExecutor::fsgnjn, x, y, 1.5.into());
    }

    #[test]
    fn fsgnjn_secret_secret() {
        let x = Float::Secret(1.5.embed().unwrap());
        let y = Float::Secret((-0.5).embed().unwrap());
        test!(MPCExecutor::fsgnjn, x, y, 1.5.into());
    }

    #[test]
    fn fsgnjx_public_public() {
        let x = Float::Public(1.5);
        let y = Float::Public(-1.0);
        test!(MPCExecutor::fsgnjx, x, y, 1.5.into());
    }

    #[test]
    fn fsgnjx_secret_public() {
        let x = Float::Secret(1.5.embed().unwrap());
        let y = Float::Public(-1.0);
        test!(MPCExecutor::fsgnjx, x, y, 1.5.into());
    }

    #[test]
    fn fsgnjx_secret_secret() {
        let x = Float::Secret(1.5.embed().unwrap());
        let y = Float::Secret((-0.5).embed().unwrap());
        test!(MPCExecutor::fsgnjx, x, y, 1.5.into());
    }

    #[test]
    fn fabs_public() {
        let x = Float::Public(-1.5);
        test!(MPCExecutor::fabs, x, 1.5.into());
    }

    #[test]
    fn fabs_secret() {
        let x = Float::Secret((-1.5).embed().unwrap());
        test!(MPCExecutor::fabs, x, 1.5.into());
    }

    #[test]
    fn fneg_public() {
        let x = Float::Public(-1.5);
        test!(MPCExecutor::fneg, x, 1.5.into());
        let x = Float::Public(1.5);
        test!(MPCExecutor::fneg, x, (-1.5).into());
    }

    #[test]
    fn fneg_secret() {
        let x = Float::Secret((-1.5).embed().unwrap());
        test!(MPCExecutor::fneg, x, 1.5.into());
        let x = Float::Secret(1.5.embed().unwrap());
        test!(MPCExecutor::fneg, x, (-1.5).into());
    }

    #[test]
    fn fsqrt_public() {
        let x = Float::Public(16.0);
        test!(MPCExecutor::fsqrt, x, 4.0.into());
    }

    #[test]
    fn fsqrt_secret() {
        let x = Float::Secret(16.0.embed().unwrap());
        test!(MPCExecutor::fsqrt, x, 4.0.into());
    }

    #[test]
    fn fexp_public() {
        let x = Float::Public(2.0);
        test!(MPCExecutor::fexp, x, E.powf(2.0).into());
    }

    #[ignore = "error too high"]
    #[test]
    fn fexp_secret() {
        let x = Float::Secret(2.0.embed().unwrap());
        test!(MPCExecutor::fexp, x, E.powf(2.0).into());
    }

    #[test]
    fn finv_public() {
        let x = Float::Public(4.0);
        test!(MPCExecutor::finv, x, (1.0 / 4.0).into());
    }

    #[test]
    fn finv_secret() {
        let x = Float::Secret(4.0.embed().unwrap());
        test!(MPCExecutor::finv, x, (1.0 / 4.0).into());
    }

    #[test]
    fn fcvtlud_public() {
        let x = Float::Public(4.2);
        test!(MPCExecutor::fcvtlud, x, 4.into());
    }

    #[ignore = "can be off by 1"]
    #[test]
    fn fcvtlud_secret() {
        let x = Float::Secret(4.2.embed().unwrap());
        test!(MPCExecutor::fcvtlud, x, 4.into());
    }

    #[test]
    fn fcvtdlu_public() {
        let x = Integer::Public(3);
        test!(MPCExecutor::fcvtdlu, x, 3.0.into());
    }

    #[test]
    fn fcvtdlu_secret() {
        let x = Integer::Secret(Share::Arithmetic(3));
        test!(MPCExecutor::fcvtdlu, x, 3.0.into());
    }

    #[test]
    fn vmul_public_public() {
        let x = [Integer::Public(3), Integer::Public(2)];
        let y = [Integer::Public(5), Integer::Public(3)];
        let expected = [15.into(), 6.into()];
        test_vec!(MPCExecutor::vmul, x, y, expected);
    }

    #[test]
    fn vmul_secret_public() {
        let x = [
            Integer::Secret(Share::Arithmetic(3)),
            Integer::Secret(Share::Arithmetic(2)),
        ];
        let y = [Integer::Public(5), Integer::Public(3)];
        let expected = [15.into(), 6.into()];
        test_vec!(MPCExecutor::vmul, x, y, expected);
    }

    #[test]
    fn vmul_secret_secret() {
        let x = [
            Integer::Secret(Share::Arithmetic(3)),
            Integer::Secret(Share::Arithmetic(2)),
        ];
        let y = [
            Integer::Secret(Share::Arithmetic(5)),
            Integer::Secret(Share::Arithmetic(3)),
        ];
        let expected = [15.into(), 6.into()];
        test_vec!(MPCExecutor::vmul, x, y, expected);
    }

    #[test]
    fn vfmul_public_public() {
        let x = [Float::Public(3.0), Float::Public(2.0)];
        let y = [Float::Public(5.0), Float::Public(3.0)];
        let expected = [15.0.into(), 6.0.into()];
        test_vec!(MPCExecutor::vfmul, x, y, expected);
    }

    #[test]
    fn vfmul_secret_public() {
        let x = [
            Float::Secret(3.0.embed().unwrap()),
            Float::Secret(2.0.embed().unwrap()),
        ];
        let y = [Float::Public(5.0), Float::Public(3.0)];
        let expected = [15.0.into(), 6.0.into()];
        test_vec!(MPCExecutor::vfmul, x, y, expected);
    }

    #[test]
    fn vfmul_secret_secret() {
        let x = [
            Float::Secret(3.0.embed().unwrap()),
            Float::Secret(2.0.embed().unwrap()),
        ];
        let y = [
            Float::Secret(5.0.embed().unwrap()),
            Float::Secret(3.0.embed().unwrap()),
        ];
        let expected = [15.0.into(), 6.0.into()];
        test_vec!(MPCExecutor::vfmul, x, y, expected);
    }

    #[test]
    fn vand_public_public() {
        let x = [Integer::Public(0x4), Integer::Public(0xa)];
        let y = [Integer::Public(0x6), Integer::Public(0x8)];
        let expected = [0x4.into(), 0x8.into()];
        test_vec!(MPCExecutor::vand, x, y, expected);
    }

    #[test]
    fn vand_secret_public() {
        let x = [
            Integer::Secret(Share::Binary(0x4)),
            Integer::Secret(Share::Binary(0xa)),
        ];
        let y = [Integer::Public(0x6), Integer::Public(0x8)];
        let expected = [0x4.into(), 0x8.into()];
        test_vec!(MPCExecutor::vand, x, y, expected);
    }

    #[test]
    fn vand_secret_secret() {
        let x = [
            Integer::Secret(Share::Binary(0x4)),
            Integer::Secret(Share::Binary(0xa)),
        ];
        let y = [
            Integer::Secret(Share::Binary(0x6)),
            Integer::Secret(Share::Binary(0x8)),
        ];
        let expected = [0x4.into(), 0x8.into()];
        test_vec!(MPCExecutor::vand, x, y, expected);
    }
}

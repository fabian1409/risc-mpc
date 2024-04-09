use crate::{
    channel::{Channel, Message},
    error::{Error, Result},
    ot::{OTReceiver, OTSender},
    party::PARTY_0,
    triple_provider::TripleProvider,
    types::{Float, Integer},
    Share,
};
use bit::BitIndex;
use log::debug;
use rand::Rng;

/// Number of AND triples needed per secret `<`, `>`, `<=`, `>=`.
/// Secret `==` and `!=` need `2 * CMP_AND_TRIPLES`.
pub const CMP_AND_TRIPLES: u64 = 13;
pub const FIXED_POINT_INTEGER_PART: u64 = 16;
const FIXED_POINT_DECIMAL_PART: u64 = 16;

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
    if (fixed_point as i64) < (1 << (FIXED_POINT_INTEGER_PART - 1))
        || (fixed_point as i64) >= -(1 << (FIXED_POINT_INTEGER_PART - 1))
    {
        Ok((fixed_point * (1 << FIXED_POINT_INTEGER_PART) as f64) as i64 as u64)
    } else {
        Err(Error::FixedPointEmbeddingError)
    }
}

pub fn to_fixed_point(embedded: u64) -> Result<f64> {
    let max = 1 << (FIXED_POINT_INTEGER_PART + FIXED_POINT_DECIMAL_PART);
    if embedded > max && embedded < (u64::MAX - max) {
        Err(Error::FixedPointEmbeddingError)
    } else {
        let scaled = if embedded > (u64::MAX - max) {
            embedded.wrapping_sub(u64::MAX)
        } else {
            embedded
        };
        let fixed_point = scaled as i64 as f64 / (1 << FIXED_POINT_INTEGER_PART) as f64;
        Ok(fixed_point)
    }
}

/// [`MPCExecutor`] handles MPC operations during execution.
#[derive(Debug)]
pub struct MPCExecutor<C: Channel> {
    id: usize,
    ch: C,
    triple_provider: TripleProvider,
}

impl<C: Channel> MPCExecutor<C> {
    /// Create new [`MPCExecutor`].
    pub fn new(id: usize, ch: C, triple_provider: TripleProvider) -> MPCExecutor<C> {
        MPCExecutor {
            id,
            ch,
            triple_provider,
        }
    }

    /// Reveal the given [`Share`].
    pub fn reveal(&mut self, share: Share) -> Result<u64> {
        if self.id == PARTY_0 {
            self.ch.send(Message::Share(share))?;
            let other = self.ch.recv()?.as_share().unwrap();
            shares_to_x((share, other))
        } else {
            let other = self.ch.recv()?.as_share().unwrap();
            self.ch.send(Message::Share(share))?;
            shares_to_x((share, other))
        }
    }

    /// Reveal the given [`Share`] for party with `id`.
    pub fn reveal_for(&mut self, share: Share, id: usize) -> Result<Option<u64>> {
        if self.id == id {
            let other = self.ch.recv()?.as_share().unwrap();
            Ok(Some(shares_to_x((share, other))?))
        } else {
            self.ch.send(Message::Share(share))?;
            Ok(None)
        }
    }

    /// Add 2 binary shares using a optimized binary addition circuit.
    fn bin_add(&mut self, x: Integer, y: Integer) -> Result<Integer> {
        debug!("bin_add x = {x:?} y = {y:?}");

        let mut s = self.and(x, y)?;
        let mut p = self.xor(x, y)?;
        let orig_p = p;

        let masks = [
            6148914691236517205,
            2459565876494606882,
            578721382704613384,
            36029346783166592,
            140737488388096,
            2147483648u64,
        ];

        let mut multipliers = Vec::new();

        for i in 0..6 {
            multipliers.push((1 << (2u64.pow(i) + 1)) - 2);
        }

        let out_masks: Vec<u64> = masks
            .iter()
            .zip(multipliers.iter())
            .map(|(mask, mult)| mask * mult)
            .collect();

        for ((in_mask, out_mask), mult) in
            masks.iter().zip(out_masks.iter()).zip(multipliers.iter())
        {
            let not_out_mask = !out_mask;
            let p0 = self.and(p, Integer::Public(*out_mask))?;
            let s1 = self.and(s, Integer::Public(*in_mask))?.as_u64();
            let p1 = self.and(p, Integer::Public(*in_mask))?.as_u64();

            let s1 = Integer::Secret(Share::Binary(s1.wrapping_mul(*mult)));
            let p1 = Integer::Secret(Share::Binary(p1.wrapping_mul(*mult)));

            p = self.and(p, Integer::Public(not_out_mask))?;

            let tmp = self.and(p0, s1)?;
            s = self.xor(s, tmp)?;

            let tmp = self.and(p0, p1)?;
            p = self.xor(p, tmp)?;
        }

        let tmp = self.lshift(s, Integer::Public(1))?;
        self.xor(orig_p, tmp)
    }

    /// Convert a [`Secret`] from a [`Arithmetic`] share to a [`Binary`] share.
    ///
    /// [`Secret`]: Value::Secret
    /// [`Arithmetic`]: Share::Arithmetic
    /// [`Binary`]: Share::Binary
    pub fn a2b(&mut self, x: Integer) -> Result<Integer> {
        debug!("a2b conversion src = {x:?}");
        if let Integer::Secret(Share::Arithmetic(share)) = x {
            // https://eprint.iacr.org/2018/403.pdf page 16
            let (a, b) = if self.id == PARTY_0 {
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
            if self.id == PARTY_0 {
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
                    inputs.push((rug::Integer::from(si0), rug::Integer::from(si1)));
                }
                let mut sender = OTSender::new();
                sender.send(&mut self.ch, &inputs)?;
                x_a = !x_a;
                x_a += 1;
                debug!("id = {} x_a = {x_a}", self.id);
                Ok(Integer::Secret(Share::Arithmetic(x_a)))
            } else {
                let mut x_a = 0u64;
                let mut receiver = OTReceiver::new();
                let mut choices = Vec::new();
                for i in 0..64 {
                    choices.push(x_b.bit(i));
                }
                let res = receiver.receive(&mut self.ch, &choices)?;
                for e in res {
                    x_a = x_a.wrapping_add(e.try_into().unwrap());
                }
                x_a = !x_a;
                debug!("id = {} x_a = {x_a}", self.id);
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
                if self.id == PARTY_0 {
                    Ok(Integer::Secret(Share::Arithmetic(x.wrapping_add(y))))
                } else {
                    Ok(Integer::Secret(Share::Arithmetic(x)))
                }
            }
            (Integer::Public(x), Integer::Secret(Share::Arithmetic(y))) => {
                if self.id == PARTY_0 {
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

    pub fn fadd(&mut self, x: Float, y: Float) -> Result<Float> {
        debug!("fadd x = {x:?} y = {y:?}");
        match (x, y) {
            (Float::Public(x), Float::Public(y)) => Ok(Float::Public(x + y)),
            (Float::Secret(x), Float::Secret(y)) => Ok(Float::Secret(x.wrapping_add(y))),
            (Float::Secret(x), Float::Public(y)) => {
                if self.id == PARTY_0 {
                    Ok(Float::Secret(x.wrapping_add(y.embed()?)))
                } else {
                    Ok(Float::Secret(x))
                }
            }
            (Float::Public(x), Float::Secret(y)) => {
                if self.id == PARTY_0 {
                    Ok(Float::Secret(x.embed()?.wrapping_add(y)))
                } else {
                    Ok(Float::Secret(0u64.wrapping_add(y)))
                }
            }
        }
    }

    pub fn addi(&mut self, x: Integer, imm: i32) -> Result<Integer> {
        debug!("addi x = {x:?} imm = {imm}");
        self.add(x, Integer::Public(imm as u64))
    }

    pub fn sub(&mut self, x: Integer, y: Integer) -> Result<Integer> {
        debug!("sub x = {x:?} y = {y:?}");
        match (x, y) {
            (Integer::Public(x), Integer::Public(y)) => Ok(Integer::Public(x.wrapping_sub(y))),
            (Integer::Secret(Share::Arithmetic(x)), Integer::Secret(Share::Arithmetic(y))) => {
                Ok(Integer::Secret(Share::Arithmetic(x.wrapping_sub(y))))
            }
            (Integer::Secret(Share::Arithmetic(x)), Integer::Public(y)) => {
                if self.id == PARTY_0 {
                    Ok(Integer::Secret(Share::Arithmetic(x.wrapping_sub(y))))
                } else {
                    Ok(Integer::Secret(Share::Arithmetic(x)))
                }
            }
            (Integer::Public(x), Integer::Secret(Share::Arithmetic(y))) => {
                if self.id == PARTY_0 {
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
                if self.id == PARTY_0 {
                    Ok(Float::Secret(x.wrapping_sub(y.embed()?)))
                } else {
                    Ok(Float::Secret(x))
                }
            }
            (Float::Public(x), Float::Secret(y)) => {
                if self.id == PARTY_0 {
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

                let d = self.reveal(d_share)?;
                let e = self.reveal(e_share)?;

                if self.id == PARTY_0 {
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

                let d = self.reveal(d_share)?;
                let e = self.reveal(e_share)?;

                let res = if self.id == PARTY_0 {
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
                // truncate after mul
                let res = self.div(res, Integer::Public(1u64 << FIXED_POINT_INTEGER_PART))?;
                Ok(Float::Secret(res.as_u64()))
            }
            (Float::Secret(y), Float::Public(x)) | (Float::Public(x), Float::Secret(y)) => {
                let res = Integer::Secret(Share::Arithmetic(x.embed()?.wrapping_mul(y)));
                // truncate after mul
                let res = self.div(res, Integer::Public(1u64 << FIXED_POINT_INTEGER_PART))?;
                Ok(Float::Secret(res.as_u64()))
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
                    let tmp = Integer::Secret(Share::Arithmetic(x / y));
                    self.sub(tmp, Integer::Public(u64::MAX / y))
                }
            }
            _ => Err(Error::DivBySecret),
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
                        x.wrapping_mul(1u64 << FIXED_POINT_INTEGER_PART),
                    )),
                    Integer::Public(y.embed()?),
                )?;
                Ok(Float::Secret(res.as_u64()))
            }
            _ => Err(Error::DivBySecret),
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
            _ => Err(Error::DivBySecret),
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
                if self.id == PARTY_0 {
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

                let d = self.reveal(d_share)?;
                let e = self.reveal(e_share)?;

                if self.id == PARTY_0 {
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
            _ => Err(Error::ShiftBySecret),
        }
    }

    pub fn rshift(&mut self, x: Integer, y: Integer) -> Result<Integer> {
        debug!("rshift x = {x:?} y = {y:?}");
        match (x, y) {
            (Integer::Public(x), Integer::Public(y)) => Ok(Integer::Public(x >> y)),
            (Integer::Secret(Share::Binary(x)), Integer::Public(y)) => {
                Ok(Integer::Secret(Share::Binary(x >> y)))
            }
            (Integer::Secret(Share::Arithmetic(x)), Integer::Public(y)) => {
                Ok(Integer::Secret(Share::Arithmetic(x >> y)))
            }
            _ => Err(Error::ShiftBySecret),
        }
    }

    pub fn lt(&mut self, x: Integer, y: Integer) -> Result<Integer> {
        match (x, y) {
            (Integer::Public(x), Integer::Public(y)) => Ok(Integer::Public((x < y) as u64)),
            (Integer::Secret(Share::Arithmetic(_)), Integer::Secret(Share::Arithmetic(_)))
            | (Integer::Secret(Share::Arithmetic(_)), Integer::Public(_))
            | (Integer::Public(_), Integer::Secret(Share::Arithmetic(_))) => {
                let z_a = self.sub(x, y)?;
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
                let z_b = self.a2b(Integer::Secret(Share::Arithmetic(z_a.as_u64().unwrap())))?;
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

    pub fn fsqrt(&mut self, x: Float) -> Result<Float> {
        debug!("fsqrt x = {x:?}");
        match x {
            Float::Public(x) => Ok(Float::Public(x.sqrt())),
            Float::Secret(x) => {
                // https://en.wikipedia.org/wiki/Fast_inverse_square_root
                // y_n+1 = 1/2 * y_n * (3 − x * y_n * y_n).
                let mut y_n = Integer::Secret(Share::Arithmetic(1));
                for _ in 0..2 {
                    let tmp = self.mul(y_n, y_n)?;
                    let tmp = self.mul(Integer::Secret(Share::Arithmetic(x)), tmp)?;
                    let tmp = self.sub(Integer::Public(3), tmp)?;
                    let tmp = self.mul(y_n, tmp)?;
                    y_n = self.div(tmp, Integer::Public(2))?;
                }
                // inv_sqrt * x
                Ok(Float::Secret(
                    self.mul(y_n, Integer::Secret(Share::Arithmetic(x)))?
                        .as_u64(),
                ))
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
                Integer::Public(1u64 << FIXED_POINT_INTEGER_PART),
            ),
        }
    }

    pub fn fcvtdlu(&mut self, x: Integer) -> Result<Float> {
        debug!("fcvt lu to d x = {x:?}");
        match x {
            Integer::Public(x) => Ok(Float::Public(x as f64)),
            Integer::Secret(_) => {
                let embedded = self.mul(x, Integer::Public(1u64 << FIXED_POINT_INTEGER_PART))?;
                Ok(Float::Secret(embedded.as_u64()))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::channel::ThreadChannel;
    use approx::assert_relative_eq;
    use std::{
        sync::mpsc::{self, Receiver, Sender},
        thread,
    };

    fn create_channels() -> (ThreadChannel, ThreadChannel) {
        let (tx0, rx0): (Sender<Message>, Receiver<Message>) = mpsc::channel();
        let (tx1, rx1): (Sender<Message>, Receiver<Message>) = mpsc::channel();
        let ch0 = ThreadChannel::new(tx0, rx1);
        let ch1 = ThreadChannel::new(tx1, rx0);
        (ch0, ch1)
    }

    fn inputs(x: Integer) -> (Integer, Integer) {
        match x {
            Integer::Secret(x) => {
                let (x0, x1) = x_to_shares(x);
                (Integer::Secret(x0), Integer::Secret(x1))
            }
            Integer::Public(_) => (x, x),
        }
    }

    fn output(executor: &mut MPCExecutor<ThreadChannel>, integer: Integer) -> u64 {
        match integer {
            Integer::Secret(share) => executor.reveal(share).unwrap(),
            Integer::Public(res) => res,
        }
    }

    fn float_output(executor: &mut MPCExecutor<ThreadChannel>, float: Float) -> f64 {
        match float {
            Float::Secret(embedded) => {
                to_fixed_point(executor.reveal(Share::Arithmetic(embedded)).unwrap()).unwrap()
            }
            Float::Public(res) => res,
        }
    }

    fn float_inputs(x: Float) -> (Float, Float) {
        match x {
            Float::Secret(x) => {
                let (x0, x1) = x_to_shares(Share::Arithmetic(x));
                (Float::Secret(x0.into()), Float::Secret(x1.into()))
            }
            Float::Public(_) => (x, x),
        }
    }
    macro_rules! run {
        ($run:expr, $x:expr, $y:expr, $expected:expr) => {{
            let (ch0, ch1) = create_channels();
            let (x0, x1) = inputs($x);
            let (y0, y1) = inputs($y);
            let party0 = thread::spawn(move || $run(0, ch0, x0, y0, $expected));
            let party1 = thread::spawn(move || $run(1, ch1, x1, y1, $expected));
            party0.join().unwrap();
            party1.join().unwrap();
        }};
        ($run:expr, $x:expr, $expected:expr) => {{
            let (ch0, ch1) = create_channels();
            let (x0, x1) = inputs($x);
            let party0 = thread::spawn(move || $run(0, ch0, x0, $expected));
            let party1 = thread::spawn(move || $run(1, ch1, x1, $expected));
            party0.join().unwrap();
            party1.join().unwrap();
        }};
    }

    macro_rules! run_float {
        ($run:expr, $x:expr, $y:expr, $expected:expr) => {{
            let (ch0, ch1) = create_channels();
            let (x0, x1) = float_inputs($x);
            let (y0, y1) = float_inputs($y);
            let party0 = thread::spawn(move || $run(0, ch0, x0, y0, $expected));
            let party1 = thread::spawn(move || $run(1, ch1, x1, y1, $expected));
            party0.join().unwrap();
            party1.join().unwrap();
        }};
        ($run:expr, $x:expr, $expected:expr) => {{
            let (ch0, ch1) = create_channels();
            let (x0, x1) = float_inputs($x);
            let party0 = thread::spawn(move || $run(0, ch0, x0, $expected));
            let party1 = thread::spawn(move || $run(1, ch1, x1, $expected));
            party0.join().unwrap();
            party1.join().unwrap();
        }};
    }

    macro_rules! test {
        (MPCExecutor::div, $x:expr, $y:expr, $expected:expr) => {{
            let run = |id: usize, ch: ThreadChannel, x: Integer, y: Integer, expected| {
                let mut executor = MPCExecutor::new(id, ch, TripleProvider::new(id));
                let value = MPCExecutor::div(&mut executor, x, y).unwrap();
                let res = output(&mut executor, value);
                assert!(res == expected || res + 1 == expected || res - 1 == expected);
            };
            run!(run, $x, $y, $expected);
        }};
        ($f:expr, $x:expr, $y:expr, $expected:expr) => {{
            let run = |id: usize, ch: ThreadChannel, x: Integer, y: Integer, expected| {
                let mut executor = MPCExecutor::new(id, ch, TripleProvider::new(id));
                let value = $f(&mut executor, x, y).unwrap();
                let res = output(&mut executor, value);
                assert_eq!(res, expected);
            };
            run!(run, $x, $y, $expected);
        }};
        ($f:expr, $x:expr, $expected:expr) => {{
            let run = |id: usize, ch: ThreadChannel, x: Integer, expected| {
                let mut executor = MPCExecutor::new(id, ch, TripleProvider::new(id));
                let value = $f(&mut executor, x).unwrap();
                let res = output(&mut executor, value);
                assert_eq!(res, expected);
            };
            run!(run, $x, $expected);
        }};
    }

    macro_rules! test_f64 {
        (MPCExecutor::fcvtlud, $x:expr, $expected:expr) => {{
            let run = |id: usize, ch: ThreadChannel, x: Float, expected| {
                let mut executor = MPCExecutor::new(id, ch, TripleProvider::new(id));
                let value = MPCExecutor::fcvtlud(&mut executor, x).unwrap();
                let res = output(&mut executor, value);
                assert!(res == expected || res + 1 == expected || res - 1 == expected);
            };
            run_float!(run, $x, $expected);
        }};
        (MPCExecutor::fcvtdlu, $x:expr, $expected:expr) => {{
            let run = |id: usize, ch: ThreadChannel, x: Integer, expected| {
                let mut executor = MPCExecutor::new(id, ch, TripleProvider::new(id));
                let value = MPCExecutor::fcvtdlu(&mut executor, x).unwrap();
                let res = float_output(&mut executor, value);
                assert_relative_eq!(res, expected, epsilon = 10e-3);
            };
            run!(run, $x, $expected);
        }};
        ($f:expr, $x:expr, $expected:expr) => {{
            let run = |id: usize, ch: ThreadChannel, x: Float, expected| {
                let mut executor = MPCExecutor::new(id, ch, TripleProvider::new(id));
                let value = $f(&mut executor, x).unwrap();
                let res = float_output(&mut executor, value);
                assert_relative_eq!(res, expected, epsilon = 10e-3);
            };
            run_float!(run, $x, $expected);
        }};
        ($f:expr, $x:expr, $y:expr, $expected:expr) => {{
            let run = |id: usize, ch: ThreadChannel, x: Float, y: Float, expected| {
                let mut executor = MPCExecutor::new(id, ch, TripleProvider::new(id));
                let value = $f(&mut executor, x, y).unwrap();
                let res = float_output(&mut executor, value);
                assert_relative_eq!(res, expected, epsilon = 10e-3);
            };
            run_float!(run, $x, $y, $expected);
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
    fn bin_add() {
        let x = Integer::Secret(Share::Binary(3));
        let y = Integer::Secret(Share::Binary(2));
        test!(MPCExecutor::bin_add, x, y, 5)
    }

    #[test]
    fn add_public_public() {
        let x = Integer::Public(3);
        let y = Integer::Public(2);
        test!(MPCExecutor::add, x, y, 5)
    }

    #[test]
    fn add_secret_public() {
        let x = Integer::Secret(Share::Arithmetic(3));
        let y = Integer::Public(2);
        test!(MPCExecutor::add, x, y, 5);
    }

    #[test]
    fn add_secret_secret() {
        let x = Integer::Secret(Share::Arithmetic(3));
        let y = Integer::Secret(Share::Arithmetic(2));
        test!(MPCExecutor::add, x, y, 5);
    }

    #[test]
    fn sub_public_public() {
        let x = Integer::Public(5);
        let y = Integer::Public(2);
        test!(MPCExecutor::sub, x, y, 3);
    }

    #[test]
    fn sub_secret_public() {
        let x = Integer::Secret(Share::Arithmetic(5));
        let y = Integer::Public(2);
        test!(MPCExecutor::sub, x, y, 3);
    }

    #[test]
    fn sub_secret_secret() {
        let x = Integer::Secret(Share::Arithmetic(5));
        let y = Integer::Secret(Share::Arithmetic(2));
        test!(MPCExecutor::sub, x, y, 3);
    }

    #[test]
    fn mul_public_public() {
        let x = Integer::Public(3);
        let y = Integer::Public(2);
        test!(MPCExecutor::mul, x, y, 6);
    }

    #[test]
    fn mul_secret_public() {
        let x = Integer::Secret(Share::Arithmetic(3));
        let y = Integer::Public(2);
        test!(MPCExecutor::mul, x, y, 6);
    }

    #[test]
    fn mul_secret_secret() {
        let x = Integer::Secret(Share::Arithmetic(3));
        let y = Integer::Secret(Share::Arithmetic(2));
        test!(MPCExecutor::mul, x, y, 6);
    }

    #[test]
    fn div_public_public() {
        let x = Integer::Public(8);
        let y = Integer::Public(2);
        test!(MPCExecutor::div, x, y, 4);
    }

    #[test]
    fn div_secret_public() {
        let x = Integer::Secret(Share::Arithmetic(8));
        let y = Integer::Public(2);
        test!(MPCExecutor::div, x, y, 4);
    }

    #[test]
    fn rem_public_public() {
        let x = Integer::Public(8);
        let y = Integer::Public(2);
        test!(MPCExecutor::rem, x, y, 0);
    }

    #[ignore = "will fail if div is off by 1"]
    #[test]
    fn rem_secret_public() {
        let x = Integer::Secret(Share::Arithmetic(8));
        let y = Integer::Public(2);
        test!(MPCExecutor::rem, x, y, 0);
    }

    #[test]
    fn xor_public_public() {
        let x = Integer::Public(0b1111);
        let y = Integer::Public(0b0110);
        test!(MPCExecutor::xor, x, y, 0b1001);
    }

    #[test]
    fn xor_secret_public() {
        let x = Integer::Secret(Share::Binary(0b1111));
        let y = Integer::Public(0b0110);
        test!(MPCExecutor::xor, x, y, 0b1001);
    }

    #[test]
    fn xor_secret_secret() {
        let x = Integer::Secret(Share::Binary(0b1111));
        let y = Integer::Secret(Share::Binary(0b0110));
        test!(MPCExecutor::xor, x, y, 0b1001);
    }

    #[test]
    fn and_public_public() {
        let x = Integer::Public(0b1111);
        let y = Integer::Public(0b0110);
        test!(MPCExecutor::and, x, y, 0b0110);
    }

    #[test]
    fn and_secret_public() {
        let x = Integer::Secret(Share::Binary(0b1111));
        let y = Integer::Public(0b0110);
        test!(MPCExecutor::and, x, y, 0b0110);
    }

    #[test]
    fn and_secret_secret() {
        let x = Integer::Secret(Share::Binary(0b1111));
        let y = Integer::Secret(Share::Binary(0b0110));
        test!(MPCExecutor::and, x, y, 0b0110);
    }

    #[test]
    fn or_public_public() {
        let x = Integer::Public(0b0100);
        let y = Integer::Public(0b0110);
        test!(MPCExecutor::or, x, y, 0b0110);
    }

    #[test]
    fn or_secret_public() {
        let x = Integer::Secret(Share::Binary(0b0100));
        let y = Integer::Public(0b0110);
        test!(MPCExecutor::or, x, y, 0b0110);
    }

    #[test]
    fn or_secret_secret() {
        let x = Integer::Secret(Share::Binary(0b0100));
        let y = Integer::Secret(Share::Binary(0b0110));
        test!(MPCExecutor::or, x, y, 0b0110);
    }

    #[test]
    fn lt_public_public() {
        let x = Integer::Public(3);
        let y = Integer::Public(5);
        test!(MPCExecutor::lt, x, y, 1);
        test!(MPCExecutor::lt, y, x, 0);
    }

    #[test]
    fn lt_public_secret() {
        let x = Integer::Public(3);
        let y = Integer::Secret(Share::Arithmetic(5));
        test!(MPCExecutor::lt, x, y, 1);
        test!(MPCExecutor::lt, y, x, 0);
    }

    #[test]
    fn lt_secret_secret() {
        let x = Integer::Secret(Share::Arithmetic(3));
        let y = Integer::Secret(Share::Arithmetic(5));
        test!(MPCExecutor::lt, x, y, 1);
        test!(MPCExecutor::lt, y, x, 0);
    }

    #[test]
    fn gt_public_public() {
        let x = Integer::Public(3);
        let y = Integer::Public(5);
        test!(MPCExecutor::gt, x, y, 0);
        test!(MPCExecutor::gt, y, x, 1);
    }

    #[test]
    fn gt_public_secret() {
        let x = Integer::Public(3);
        let y = Integer::Secret(Share::Arithmetic(5));
        test!(MPCExecutor::gt, x, y, 0);
        test!(MPCExecutor::gt, y, x, 1);
    }

    #[test]
    fn gt_secret_secret() {
        let x = Integer::Secret(Share::Arithmetic(3));
        let y = Integer::Secret(Share::Arithmetic(5));
        test!(MPCExecutor::gt, x, y, 0);
        test!(MPCExecutor::gt, y, x, 1);
    }

    #[test]
    fn le_public_public() {
        let x = Integer::Public(3);
        let y = Integer::Public(5);
        test!(MPCExecutor::le, x, y, 1);
        test!(MPCExecutor::le, y, x, 0);
        let x = Integer::Public(5);
        let y = Integer::Public(5);
        test!(MPCExecutor::le, x, y, 1);
    }

    #[test]
    fn le_public_secret() {
        let x = Integer::Public(3);
        let y = Integer::Secret(Share::Arithmetic(5));
        test!(MPCExecutor::le, x, y, 1);
        test!(MPCExecutor::le, y, x, 0);
        let x = Integer::Public(5);
        let y = Integer::Secret(Share::Arithmetic(5));
        test!(MPCExecutor::le, x, y, 1);
    }

    #[test]
    fn le_secret_secret() {
        let x = Integer::Secret(Share::Arithmetic(3));
        let y = Integer::Secret(Share::Arithmetic(5));
        test!(MPCExecutor::le, x, y, 1);
        test!(MPCExecutor::le, y, x, 0);
        let x = Integer::Secret(Share::Arithmetic(5));
        let y = Integer::Secret(Share::Arithmetic(5));
        test!(MPCExecutor::le, x, y, 1);
    }

    #[test]
    fn ge_public_public() {
        let x = Integer::Public(3);
        let y = Integer::Public(5);
        test!(MPCExecutor::ge, x, y, 0);
        test!(MPCExecutor::ge, y, x, 1);
        let x = Integer::Public(5);
        let y = Integer::Public(5);
        test!(MPCExecutor::ge, x, y, 1);
    }

    #[test]
    fn ge_public_secret() {
        let x = Integer::Public(3);
        let y = Integer::Secret(Share::Arithmetic(5));
        test!(MPCExecutor::ge, x, y, 0);
        test!(MPCExecutor::ge, y, x, 1);
        let x = Integer::Public(5);
        let y = Integer::Secret(Share::Arithmetic(5));
        test!(MPCExecutor::ge, x, y, 1);
    }

    #[test]
    fn ge_secret_secret() {
        let x = Integer::Secret(Share::Arithmetic(3));
        let y = Integer::Secret(Share::Arithmetic(5));
        test!(MPCExecutor::ge, x, y, 0);
        test!(MPCExecutor::ge, y, x, 1);
        let x = Integer::Secret(Share::Arithmetic(5));
        let y = Integer::Secret(Share::Arithmetic(5));
        test!(MPCExecutor::ge, x, y, 1);
    }

    #[test]
    fn eq_public_public() {
        let x = Integer::Public(3);
        let y = Integer::Public(5);
        test!(MPCExecutor::eq, x, y, 0);
        let x = Integer::Public(5);
        let y = Integer::Public(5);
        test!(MPCExecutor::eq, x, y, 1);
    }

    #[test]
    fn eq_public_secret() {
        let x = Integer::Public(3);
        let y = Integer::Secret(Share::Arithmetic(5));
        test!(MPCExecutor::eq, x, y, 0);
        let x = Integer::Public(5);
        let y = Integer::Secret(Share::Arithmetic(5));
        test!(MPCExecutor::eq, x, y, 1);
    }

    #[test]
    fn eq_secret_secret() {
        let x = Integer::Secret(Share::Arithmetic(3));
        let y = Integer::Secret(Share::Arithmetic(5));
        test!(MPCExecutor::eq, x, y, 0);
        let x = Integer::Secret(Share::Arithmetic(5));
        let y = Integer::Secret(Share::Arithmetic(5));
        test!(MPCExecutor::eq, x, y, 1);
    }

    #[test]
    fn neq_public_public() {
        let x = Integer::Public(3);
        let y = Integer::Public(5);
        test!(MPCExecutor::neq, x, y, 1);
        let x = Integer::Public(5);
        let y = Integer::Public(5);
        test!(MPCExecutor::neq, x, y, 0);
    }

    #[test]
    fn neq_public_secret() {
        let x = Integer::Public(3);
        let y = Integer::Secret(Share::Arithmetic(5));
        test!(MPCExecutor::neq, x, y, 1);
        let x = Integer::Public(5);
        let y = Integer::Secret(Share::Arithmetic(5));
        test!(MPCExecutor::neq, x, y, 0);
    }

    #[test]
    fn neq_secret_secret() {
        let x = Integer::Secret(Share::Arithmetic(3));
        let y = Integer::Secret(Share::Arithmetic(5));
        test!(MPCExecutor::neq, x, y, 1);
        let x = Integer::Secret(Share::Arithmetic(5));
        let y = Integer::Secret(Share::Arithmetic(5));
        test!(MPCExecutor::neq, x, y, 0);
    }

    #[test]
    fn a2b() {
        let x = Integer::Secret(Share::Arithmetic(42));
        test!(MPCExecutor::a2b, x, 42)
    }

    #[test]
    fn b2a() {
        let x = Integer::Secret(Share::Binary(42));
        test!(MPCExecutor::b2a, x, 42)
    }

    #[test]
    fn fadd_public_public() {
        let x = Float::Public(1.5);
        let y = Float::Public(0.5);
        test_f64!(MPCExecutor::fadd, x, y, 2.0);
    }

    #[test]
    fn fadd_secret_public() {
        let x = Float::Secret(1.5.embed().unwrap());
        let y = Float::Public(0.5);
        test_f64!(MPCExecutor::fadd, x, y, 2.0);
    }

    #[test]
    fn fadd_secret_secret() {
        let x = Float::Secret(1.5.embed().unwrap());
        let y = Float::Secret(0.5.embed().unwrap());
        test_f64!(MPCExecutor::fadd, x, y, 2.0);
    }

    #[test]
    fn fsub_public_public() {
        let x = Float::Public(1.5);
        let y = Float::Public(0.5);
        test_f64!(MPCExecutor::fsub, x, y, 1.0);
    }

    #[test]
    fn fsub_secret_public() {
        let x = Float::Secret(1.5.embed().unwrap());
        let y = Float::Public(0.5);
        test_f64!(MPCExecutor::fsub, x, y, 1.0);
    }

    #[test]
    fn fsub_secret_secret() {
        let x = Float::Secret(1.5.embed().unwrap());
        let y = Float::Secret(0.5.embed().unwrap());
        test_f64!(MPCExecutor::fsub, x, y, 1.0);
    }

    #[test]
    fn fmul_public_public() {
        let x = Float::Public(1.5);
        let y = Float::Public(0.5);
        test_f64!(MPCExecutor::fmul, x, y, 0.75);
    }

    #[test]
    fn fmul_secret_public() {
        let x = Float::Secret(1.5.embed().unwrap());
        let y = Float::Public(0.5);
        test_f64!(MPCExecutor::fmul, x, y, 0.75);
    }

    #[test]
    fn fdiv_public_public() {
        let x = Float::Public(7.0);
        let y = Float::Public(2.0);
        test_f64!(MPCExecutor::fdiv, x, y, 3.5);
    }

    #[test]
    fn fdiv_secret_public() {
        let x = Float::Secret(7.0.embed().unwrap());
        let y = Float::Public(2.0);
        test_f64!(MPCExecutor::fdiv, x, y, 3.5);
    }

    #[test]
    fn fmul_secret_secret() {
        let x = Float::Secret(1.5.embed().unwrap());
        let y = Float::Secret(0.5.embed().unwrap());
        test_f64!(MPCExecutor::fmul, x, y, 0.75);
    }

    #[test]
    fn fmin_public_public() {
        let x = Float::Public(1.5);
        let y = Float::Public(0.5);
        test_f64!(MPCExecutor::fmin, x, y, 0.5);
    }

    #[test]
    fn fmin_secret_public() {
        let x = Float::Secret(1.5.embed().unwrap());
        let y = Float::Public(0.5);
        test_f64!(MPCExecutor::fmin, x, y, 0.5);
    }

    #[test]
    fn fmin_secret_secret() {
        let x = Float::Secret(1.5.embed().unwrap());
        let y = Float::Secret(0.5.embed().unwrap());
        test_f64!(MPCExecutor::fmin, x, y, 0.5);
    }

    #[test]
    fn fmax_public_public() {
        let x = Float::Public(1.5);
        let y = Float::Public(0.5);
        test_f64!(MPCExecutor::fmax, x, y, 1.5);
    }

    #[test]
    fn fmax_secret_public() {
        let x = Float::Secret(1.5.embed().unwrap());
        let y = Float::Public(0.5);
        test_f64!(MPCExecutor::fmax, x, y, 1.5);
    }

    #[test]
    fn fmax_secret_secret() {
        let x = Float::Secret(1.5.embed().unwrap());
        let y = Float::Secret(0.5.embed().unwrap());
        test_f64!(MPCExecutor::fmax, x, y, 1.5);
    }

    #[test]
    fn fsgnj_public_public() {
        let x = Float::Public(1.5);
        let y = Float::Public(-1.0);
        test_f64!(MPCExecutor::fsgnj, x, y, -1.5);
    }

    #[test]
    fn fsgnj_secret_public() {
        let x = Float::Secret(1.5.embed().unwrap());
        let y = Float::Public(-1.0);
        test_f64!(MPCExecutor::fsgnj, x, y, -1.5);
    }

    #[test]
    fn fsgnj_secret_secret() {
        let x = Float::Secret(1.5.embed().unwrap());
        let y = Float::Secret((-0.5).embed().unwrap());
        test_f64!(MPCExecutor::fsgnj, x, y, -1.5);
    }

    #[test]
    fn fsgnjn_public_public() {
        let x = Float::Public(1.5);
        let y = Float::Public(-1.0);
        test_f64!(MPCExecutor::fsgnjn, x, y, 1.5);
    }

    #[test]
    fn fsgnjn_secret_public() {
        let x = Float::Secret(1.5.embed().unwrap());
        let y = Float::Public(-1.0);
        test_f64!(MPCExecutor::fsgnjn, x, y, 1.5);
    }

    #[test]
    fn fsgnjn_secret_secret() {
        let x = Float::Secret(1.5.embed().unwrap());
        let y = Float::Secret((-0.5).embed().unwrap());
        test_f64!(MPCExecutor::fsgnjn, x, y, 1.5);
    }

    #[test]
    fn fsgnjx_public_public() {
        let x = Float::Public(1.5);
        let y = Float::Public(-1.0);
        test_f64!(MPCExecutor::fsgnjx, x, y, 1.5);
    }

    #[test]
    fn fsgnjx_secret_public() {
        let x = Float::Secret(1.5.embed().unwrap());
        let y = Float::Public(-1.0);
        test_f64!(MPCExecutor::fsgnjx, x, y, 1.5);
    }

    #[test]
    fn fsgnjx_secret_secret() {
        let x = Float::Secret(1.5.embed().unwrap());
        let y = Float::Secret((-0.5).embed().unwrap());
        test_f64!(MPCExecutor::fsgnjx, x, y, 1.5);
    }

    #[test]
    fn fabs_public() {
        let x = Float::Public(-1.5);
        test_f64!(MPCExecutor::fabs, x, 1.5);
    }

    #[test]
    fn fabs_secret() {
        let x = Float::Secret((-1.5).embed().unwrap());
        test_f64!(MPCExecutor::fabs, x, 1.5);
    }

    #[test]
    fn fsqrt_public() {
        let x = Float::Public(16.0);
        test_f64!(MPCExecutor::fsqrt, x, 4.0);
    }

    #[ignore = "not finished"]
    #[test]
    fn fsqrt_secret() {
        let x = Float::Secret(16.0.embed().unwrap());
        test_f64!(MPCExecutor::fsqrt, x, 4.0);
    }

    #[test]
    fn fcvtlud_public() {
        let x = Float::Public(4.2);
        test_f64!(MPCExecutor::fcvtlud, x, 4);
    }

    #[test]
    fn fcvtlud_secret() {
        let x = Float::Secret(4.2.embed().unwrap());
        test_f64!(MPCExecutor::fcvtlud, x, 4);
    }

    #[test]
    fn fcvtdlu_public() {
        let x = Integer::Public(3);
        test_f64!(MPCExecutor::fcvtdlu, x, 3.0);
    }

    #[test]
    fn fcvtdlu_secret() {
        let x = Integer::Secret(Share::Arithmetic(3));
        test_f64!(MPCExecutor::fcvtdlu, x, 3.0);
    }
}

use crate::{
    channel::{Channel, Message},
    error::{Error, Result},
    ot::{OTReceiver, OTSender},
    party::PARTY_0,
    triple_provider::TripleProvider,
    Share, Value,
};
use bit::BitIndex;
use log::debug;
use rand::Rng;
use rug::Integer;

/// Number of AND triples needed per secret `<`, `>`, `<=`, `>=`.
/// Secret `==` and `!=` need `2 * CMP_AND_TRIPLES`.
pub const CMP_AND_TRIPLES: u64 = 13;

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
    fn bin_add(&mut self, x: Value, y: Value) -> Result<Value> {
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
            let p0 = self.and(p, Value::Public(*out_mask))?;
            let s1: u64 = self.and(s, Value::Public(*in_mask))?.into();
            let p1: u64 = self.and(p, Value::Public(*in_mask))?.into();

            let s1 = Value::Secret(Share::Binary(s1.wrapping_mul(*mult)));
            let p1 = Value::Secret(Share::Binary(p1.wrapping_mul(*mult)));

            p = self.and(p, Value::Public(not_out_mask))?;

            let tmp = self.and(p0, s1)?;
            s = self.xor(s, tmp)?;

            let tmp = self.and(p0, p1)?;
            p = self.xor(p, tmp)?;
        }

        let tmp = self.lshift(s, Value::Public(1))?;
        self.xor(orig_p, tmp)
    }

    /// Convert a [`Secret`] from a [`Arithmetic`] share to a [`Binary`] share.
    ///
    /// [`Secret`]: Value::Secret
    /// [`Arithmetic`]: Share::Arithmetic
    /// [`Binary`]: Share::Binary
    pub fn a2b(&mut self, x: Value) -> Result<Value> {
        debug!("a2b conversion src = {x:?}");
        if let Value::Secret(Share::Arithmetic(share)) = x {
            // https://eprint.iacr.org/2018/403.pdf page 16
            let (a, b) = if self.id == PARTY_0 {
                (Share::Binary(share), Share::Binary(0))
            } else {
                (Share::Binary(0), Share::Binary(share))
            };

            self.bin_add(Value::Secret(a), Value::Secret(b))
        } else {
            Ok(x)
        }
    }

    /// Convert a [`Secret`] from a [`Binary`] share to a [`Arithmetic`] share.
    ///
    /// [`Secret`]: Value::Secret
    /// [`Arithmetic`]: Share::Arithmetic
    /// [`Binary`]: Share::Binary
    pub fn b2a(&mut self, x: Value) -> Result<Value> {
        if let Value::Secret(Share::Binary(x_b)) = x {
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
                    inputs.push((Integer::from(si0), Integer::from(si1)));
                }
                let mut sender = OTSender::new();
                sender.send(&mut self.ch, &inputs)?;
                x_a = !x_a;
                x_a += 1;
                debug!("id = {} x_a = {x_a}", self.id);
                Ok(Value::Secret(Share::Arithmetic(x_a)))
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
                Ok(Value::Secret(Share::Arithmetic(x_a)))
            }
        } else {
            Ok(x)
        }
    }

    pub fn add(&mut self, x: Value, y: Value) -> Result<Value> {
        debug!("add x = {x:?} y = {y:?}");
        match (x, y) {
            (Value::Public(x), Value::Public(y)) => Ok(Value::Public(x.wrapping_add(y))),
            (Value::Secret(Share::Arithmetic(x)), Value::Secret(Share::Arithmetic(y))) => {
                Ok(Value::Secret(Share::Arithmetic(x.wrapping_add(y))))
            }
            (Value::Secret(Share::Arithmetic(x)), Value::Public(y)) => {
                if self.id == PARTY_0 {
                    Ok(Value::Secret(Share::Arithmetic(x.wrapping_add(y))))
                } else {
                    Ok(Value::Secret(Share::Arithmetic(x)))
                }
            }
            (Value::Public(x), Value::Secret(Share::Arithmetic(y))) => {
                if self.id == PARTY_0 {
                    Ok(Value::Secret(Share::Arithmetic(x.wrapping_add(y))))
                } else {
                    Ok(Value::Secret(Share::Arithmetic(0u64.wrapping_add(y))))
                }
            }
            _ => {
                let x = self.b2a(x)?;
                let y = self.b2a(y)?;
                self.add(x, y)
            }
        }
    }

    pub fn addi(&mut self, x: Value, imm: i32) -> Result<Value> {
        debug!("addi x = {x:?} imm = {imm}");
        self.add(x, Value::Public(imm as u64))
    }

    pub fn sub(&mut self, x: Value, y: Value) -> Result<Value> {
        debug!("sub x = {x:?} y = {y:?}");
        match (x, y) {
            (Value::Public(x), Value::Public(y)) => Ok(Value::Public(x.wrapping_sub(y))),
            (Value::Secret(Share::Arithmetic(x)), Value::Secret(Share::Arithmetic(y))) => {
                Ok(Value::Secret(Share::Arithmetic(x.wrapping_sub(y))))
            }
            (Value::Secret(Share::Arithmetic(x)), Value::Public(y)) => {
                if self.id == PARTY_0 {
                    Ok(Value::Secret(Share::Arithmetic(x.wrapping_sub(y))))
                } else {
                    Ok(Value::Secret(Share::Arithmetic(x)))
                }
            }
            (Value::Public(x), Value::Secret(Share::Arithmetic(y))) => {
                if self.id == PARTY_0 {
                    Ok(Value::Secret(Share::Arithmetic(x.wrapping_sub(y))))
                } else {
                    Ok(Value::Secret(Share::Arithmetic(0u64.wrapping_sub(y))))
                }
            }
            _ => {
                let x = self.b2a(x)?;
                let y = self.b2a(y)?;
                self.sub(x, y)
            }
        }
    }

    pub fn mul(&mut self, x: Value, y: Value) -> Result<Value> {
        debug!("mul x = {x:?} y = {y:?}");
        match (x, y) {
            (Value::Public(x), Value::Public(y)) => Ok(Value::Public(x.wrapping_mul(y))),
            (Value::Secret(Share::Arithmetic(x)), Value::Secret(Share::Arithmetic(y))) => {
                let (a, b, c) = self
                    .triple_provider
                    .mul_triple()
                    .ok_or(Error::BeaverTripleError)?;
                let d_share = Share::Arithmetic(x.wrapping_sub(a));
                let e_share = Share::Arithmetic(y.wrapping_sub(b));

                let d = self.reveal(d_share)?;
                let e = self.reveal(e_share)?;

                if self.id == PARTY_0 {
                    Ok(Value::Secret(Share::Arithmetic(
                        c.wrapping_add(d.wrapping_mul(y))
                            .wrapping_add(e.wrapping_mul(x))
                            .wrapping_sub(d.wrapping_mul(e)),
                    )))
                } else {
                    Ok(Value::Secret(Share::Arithmetic(
                        c.wrapping_add(d.wrapping_mul(y))
                            .wrapping_add(e.wrapping_mul(x)),
                    )))
                }
            }
            (Value::Secret(Share::Arithmetic(x)), Value::Public(y))
            | (Value::Public(x), Value::Secret(Share::Arithmetic(y))) => {
                Ok(Value::Secret(Share::Arithmetic(x.wrapping_mul(y))))
            }
            _ => {
                let x = self.b2a(x)?;
                let y = self.b2a(y)?;
                self.mul(x, y)
            }
        }
    }

    pub fn div(&mut self, x: Value, y: Value) -> Result<Value> {
        debug!("div x = {x:?} y = {y:?}");
        match (x, y) {
            (Value::Public(x), Value::Public(y)) => {
                if y == 0 {
                    Err(Error::DivByZero)
                } else {
                    Ok(Value::Public(x / y))
                }
            }
            (Value::Secret(Share::Arithmetic(x)), Value::Public(y)) => {
                if y == 0 {
                    Err(Error::DivByZero)
                } else {
                    let tmp = Value::Secret(Share::Arithmetic(x / y));
                    self.sub(tmp, Value::Public(u64::MAX / y))
                }
            }
            _ => Err(Error::DivBySecretValue),
        }
    }

    pub fn rem(&mut self, x: Value, y: Value) -> Result<Value> {
        debug!("rem x = {x:?} y = {y:?}");
        match (x, y) {
            (Value::Public(x), Value::Public(y)) => Ok(Value::Public(x % y)),
            (Value::Secret(_), Value::Public(_)) => {
                let div = self.div(x, y)?;
                let mul = self.mul(div, y)?;
                self.sub(x, mul)
            }
            _ => Err(Error::DivBySecretValue),
        }
    }

    pub fn xor(&mut self, x: Value, y: Value) -> Result<Value> {
        debug!("xor x = {x:?} y = {y:?}");
        match (x, y) {
            (Value::Public(x), Value::Public(y)) => Ok(Value::Public(x ^ y)),
            (Value::Secret(Share::Binary(x)), Value::Secret(Share::Binary(y))) => {
                Ok(Value::Secret(Share::Binary(x ^ y)))
            }
            (Value::Secret(Share::Binary(x)), Value::Public(y))
            | (Value::Public(y), Value::Secret(Share::Binary(x))) => {
                if self.id == PARTY_0 {
                    Ok(Value::Secret(Share::Binary(x ^ y)))
                } else {
                    Ok(Value::Secret(Share::Binary(x)))
                }
            }
            _ => {
                let x = self.a2b(x)?;
                let y = self.a2b(y)?;
                self.xor(x, y)
            }
        }
    }

    pub fn xori(&mut self, x: Value, imm: i32) -> Result<Value> {
        debug!("xori x = {x:?} imm = {imm}");
        self.xor(x, Value::Public(imm as u64))
    }

    pub fn and(&mut self, x: Value, y: Value) -> Result<Value> {
        debug!("and x = {x:?} y = {y:?}");
        match (x, y) {
            (Value::Public(x), Value::Public(y)) => Ok(Value::Public(x & y)),
            (Value::Secret(Share::Binary(x)), Value::Secret(Share::Binary(y))) => {
                let (a, b, c) = self
                    .triple_provider
                    .and_triple()
                    .ok_or(Error::BeaverTripleError)?;
                let d_share = Share::Binary(x ^ a);
                let e_share = Share::Binary(y ^ b);

                let d = self.reveal(d_share)?;
                let e = self.reveal(e_share)?;

                if self.id == PARTY_0 {
                    Ok(Value::Secret(Share::Binary(
                        (d & y) ^ (e & x) ^ (e & d) ^ c,
                    )))
                } else {
                    Ok(Value::Secret(Share::Binary((d & y) ^ (e & x) ^ c)))
                }
            }
            (Value::Secret(Share::Binary(x)), Value::Public(y))
            | (Value::Public(x), Value::Secret(Share::Binary(y))) => {
                Ok(Value::Secret(Share::Binary(x & y)))
            }
            _ => {
                let x = self.a2b(x)?;
                let y = self.a2b(y)?;
                self.and(x, y)
            }
        }
    }

    pub fn andi(&mut self, x: Value, imm: i32) -> Result<Value> {
        debug!("andi x = {x:?} imm = {imm}");
        self.and(x, Value::Public(imm as u64))
    }

    pub fn or(&mut self, x: Value, y: Value) -> Result<Value> {
        debug!("or x = {x:?} y = {y:?}");
        match (x, y) {
            (Value::Public(x), Value::Public(y)) => Ok(Value::Public(x | y)),
            (Value::Secret(Share::Binary(_)), Value::Secret(Share::Binary(_)))
            | (Value::Secret(Share::Binary(_)), Value::Public(_))
            | (Value::Public(_), Value::Secret(Share::Binary(_))) => {
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

    pub fn ori(&mut self, x: Value, imm: i32) -> Result<Value> {
        debug!("ori x = {x:?} imm = {imm}");
        self.or(x, Value::Public(imm as u64))
    }

    pub fn lshift(&mut self, x: Value, y: Value) -> Result<Value> {
        debug!("lshift x = {x:?} y = {y:?}");
        match (x, y) {
            (Value::Public(x), Value::Public(y)) => Ok(Value::Public(x << y)),
            (Value::Secret(Share::Binary(x)), Value::Public(y)) => {
                Ok(Value::Secret(Share::Binary(x << y)))
            }
            (Value::Secret(Share::Arithmetic(x)), Value::Public(y)) => {
                Ok(Value::Secret(Share::Arithmetic(x << y)))
            }
            _ => Err(Error::ShiftBySecretValue),
        }
    }

    pub fn rshift(&mut self, x: Value, y: Value) -> Result<Value> {
        debug!("rshift x = {x:?} y = {y:?}");
        match (x, y) {
            (Value::Public(x), Value::Public(y)) => Ok(Value::Public(x >> y)),
            (Value::Secret(Share::Binary(x)), Value::Public(y)) => {
                Ok(Value::Secret(Share::Binary(x >> y)))
            }
            (Value::Secret(Share::Arithmetic(x)), Value::Public(y)) => {
                Ok(Value::Secret(Share::Arithmetic(x >> y)))
            }
            _ => Err(Error::ShiftBySecretValue),
        }
    }

    pub fn lt(&mut self, x: Value, y: Value) -> Result<Value> {
        match (x, y) {
            (Value::Public(x), Value::Public(y)) => Ok(Value::Public((x < y) as u64)),
            (Value::Secret(Share::Arithmetic(_)), Value::Secret(Share::Arithmetic(_)))
            | (Value::Secret(Share::Arithmetic(_)), Value::Public(_))
            | (Value::Public(_), Value::Secret(Share::Arithmetic(_))) => {
                let z_a = self.sub(x, y)?;
                let z_b = self.a2b(z_a)?;
                self.rshift(z_b, Value::Public(63))
            }
            _ => {
                let x = self.b2a(x)?;
                let y = self.b2a(y)?;
                self.lt(x, y)
            }
        }
    }

    pub fn gt(&mut self, x: Value, y: Value) -> Result<Value> {
        debug!("gt x = {x:?} y = {y:?}");
        self.lt(y, x)
    }

    pub fn le(&mut self, x: Value, y: Value) -> Result<Value> {
        debug!("le x = {x:?} y = {y:?}");
        let gt = self.gt(x, y)?;
        self.sub(Value::Public(1), gt)
    }

    #[allow(dead_code)]
    pub fn ge(&mut self, x: Value, y: Value) -> Result<Value> {
        debug!("ge x = {x:?} y = {y:?}");
        let lt = self.lt(x, y)?;
        self.sub(Value::Public(1), lt)
    }

    pub fn eq(&mut self, x: Value, y: Value) -> Result<Value> {
        debug!("eq x = {x:?} y = {y:?}");
        let le = self.le(x, y)?;
        let lt = self.lt(x, y)?;
        self.sub(le, lt)
    }

    pub fn neq(&mut self, x: Value, y: Value) -> Result<Value> {
        debug!("neq x = {x:?} y = {y:?}");
        let eq = self.eq(x, y)?;
        self.sub(Value::Public(1), eq)
    }

    pub fn blt(&mut self, x: Value, y: Value) -> Result<bool> {
        match self.lt(x, y)? {
            Value::Secret(share) => Ok(self.reveal(share)? != 0),
            Value::Public(lt) => Ok(lt != 0),
        }
    }

    pub fn bgt(&mut self, x: Value, y: Value) -> Result<bool> {
        debug!("gt x = {x:?} y = {y:?}");
        self.blt(y, x)
    }

    pub fn ble(&mut self, x: Value, y: Value) -> Result<bool> {
        debug!("le x = {x:?} y = {y:?}");
        let gt = self.bgt(x, y)?;
        Ok(!gt)
    }

    pub fn bge(&mut self, x: Value, y: Value) -> Result<bool> {
        debug!("ge x = {x:?} y = {y:?}");
        let lt = self.blt(x, y)?;
        Ok(!lt)
    }

    pub fn beq(&mut self, x: Value, y: Value) -> Result<bool> {
        debug!("eq x = {x:?} y = {y:?}");
        let le = self.ble(x, y)?;
        let lt = self.blt(x, y)?;
        Ok(le && !lt)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::channel::ThreadChannel;
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

    fn inputs(x: Value) -> (Value, Value) {
        match x {
            Value::Secret(x) => {
                let (x0, x1) = x_to_shares(x);
                (Value::Secret(x0), Value::Secret(x1))
            }
            Value::Public(_) => (x, x),
        }
    }

    macro_rules! test {
        ($f:expr, $x:expr, $y:expr, $expected:expr) => {{
            let run = |id: usize, ch: ThreadChannel, x: Value, y: Value, expected| {
                let mut executor = MPCExecutor::new(id, ch, TripleProvider::new(id));
                let value = $f(&mut executor, x, y).unwrap();
                let res = match value {
                    Value::Secret(share) => executor.reveal(share).unwrap(),
                    Value::Public(res) => res,
                };
                assert_eq!(res, expected);
            };
            let (ch0, ch1) = create_channels();
            let (x0, x1) = inputs($x);
            let (y0, y1) = inputs($y);
            let party0 = thread::spawn(move || run(0, ch0, x0, y0, $expected));
            let party1 = thread::spawn(move || run(1, ch1, x1, y1, $expected));
            party0.join().unwrap();
            party1.join().unwrap();
        }};
        ($f:expr, $x:expr, $expected:expr) => {{
            let run = |id: usize, ch: ThreadChannel, x: Value, expected| {
                let mut executor = MPCExecutor::new(id, ch, TripleProvider::new(id));
                let value = $f(&mut executor, x).unwrap();
                let res = match value {
                    Value::Secret(share) => executor.reveal(share).unwrap(),
                    Value::Public(res) => res,
                };
                assert_eq!(res, expected);
            };
            let (ch0, ch1) = create_channels();
            let (x0, x1) = inputs($x);
            let party0 = thread::spawn(move || run(0, ch0, x0, $expected));
            let party1 = thread::spawn(move || run(1, ch1, x1, $expected));
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
    fn bin_add() {
        let x = Value::Secret(Share::Binary(3));
        let y = Value::Secret(Share::Binary(2));
        test!(MPCExecutor::bin_add, x, y, 5)
    }

    #[test]
    fn add_public_public() {
        let x = Value::Public(3);
        let y = Value::Public(2);
        test!(MPCExecutor::add, x, y, 5)
    }

    #[test]
    fn add_secret_public() {
        let x = Value::Secret(Share::Arithmetic(3));
        let y = Value::Public(2);
        test!(MPCExecutor::add, x, y, 5);
    }

    #[test]
    fn add_secret_secret() {
        let x = Value::Secret(Share::Arithmetic(3));
        let y = Value::Secret(Share::Arithmetic(2));
        test!(MPCExecutor::add, x, y, 5);
    }

    #[test]
    fn sub_public_public() {
        let x = Value::Public(5);
        let y = Value::Public(2);
        test!(MPCExecutor::sub, x, y, 3);
    }

    #[test]
    fn sub_secret_public() {
        let x = Value::Secret(Share::Arithmetic(5));
        let y = Value::Public(2);
        test!(MPCExecutor::sub, x, y, 3);
    }

    #[test]
    fn sub_secret_secret() {
        let x = Value::Secret(Share::Arithmetic(5));
        let y = Value::Secret(Share::Arithmetic(2));
        test!(MPCExecutor::sub, x, y, 3);
    }

    #[test]
    fn mul_public_public() {
        let x = Value::Public(3);
        let y = Value::Public(2);
        test!(MPCExecutor::mul, x, y, 6);
    }

    #[test]
    fn mul_secret_public() {
        let x = Value::Secret(Share::Arithmetic(3));
        let y = Value::Public(2);
        test!(MPCExecutor::mul, x, y, 6);
    }

    #[test]
    fn mul_secret_secret() {
        let x = Value::Secret(Share::Arithmetic(3));
        let y = Value::Secret(Share::Arithmetic(2));
        test!(MPCExecutor::mul, x, y, 6);
    }

    #[test]
    fn div_public_public() {
        let x = Value::Public(8);
        let y = Value::Public(2);
        test!(MPCExecutor::div, x, y, 4);
    }

    #[ignore = "can be off by 1"]
    #[test]
    fn div_secret_public() {
        let x = Value::Secret(Share::Arithmetic(8));
        let y = Value::Public(2);
        test!(MPCExecutor::div, x, y, 4);
    }

    #[test]
    fn rem_public_public() {
        let x = Value::Public(8);
        let y = Value::Public(2);
        test!(MPCExecutor::rem, x, y, 0);
    }

    #[ignore = "will fail if div is off by 1"]
    #[test]
    fn rem_secret_public() {
        let x = Value::Secret(Share::Arithmetic(8));
        let y = Value::Public(2);
        test!(MPCExecutor::rem, x, y, 0);
    }

    #[test]
    fn xor_public_public() {
        let x = Value::Public(0b1111);
        let y = Value::Public(0b0110);
        test!(MPCExecutor::xor, x, y, 0b1001);
    }

    #[test]
    fn xor_secret_public() {
        let x = Value::Secret(Share::Binary(0b1111));
        let y = Value::Public(0b0110);
        test!(MPCExecutor::xor, x, y, 0b1001);
    }

    #[test]
    fn xor_secret_secret() {
        let x = Value::Secret(Share::Binary(0b1111));
        let y = Value::Secret(Share::Binary(0b0110));
        test!(MPCExecutor::xor, x, y, 0b1001);
    }

    #[test]
    fn and_public_public() {
        let x = Value::Public(0b1111);
        let y = Value::Public(0b0110);
        test!(MPCExecutor::and, x, y, 0b0110);
    }

    #[test]
    fn and_secret_public() {
        let x = Value::Secret(Share::Binary(0b1111));
        let y = Value::Public(0b0110);
        test!(MPCExecutor::and, x, y, 0b0110);
    }

    #[test]
    fn and_secret_secret() {
        let x = Value::Secret(Share::Binary(0b1111));
        let y = Value::Secret(Share::Binary(0b0110));
        test!(MPCExecutor::and, x, y, 0b0110);
    }

    #[test]
    fn or_public_public() {
        let x = Value::Public(0b0100);
        let y = Value::Public(0b0110);
        test!(MPCExecutor::or, x, y, 0b0110);
    }

    #[test]
    fn or_secret_public() {
        let x = Value::Secret(Share::Binary(0b0100));
        let y = Value::Public(0b0110);
        test!(MPCExecutor::or, x, y, 0b0110);
    }

    #[test]
    fn or_secret_secret() {
        let x = Value::Secret(Share::Binary(0b0100));
        let y = Value::Secret(Share::Binary(0b0110));
        test!(MPCExecutor::or, x, y, 0b0110);
    }

    #[test]
    fn lt_public_public() {
        let x = Value::Public(3);
        let y = Value::Public(5);
        test!(MPCExecutor::lt, x, y, 1);
        test!(MPCExecutor::lt, y, x, 0);
    }

    #[test]
    fn lt_public_secret() {
        let x = Value::Public(3);
        let y = Value::Secret(Share::Arithmetic(5));
        test!(MPCExecutor::lt, x, y, 1);
        test!(MPCExecutor::lt, y, x, 0);
    }

    #[test]
    fn lt_secret_secret() {
        let x = Value::Secret(Share::Arithmetic(3));
        let y = Value::Secret(Share::Arithmetic(5));
        test!(MPCExecutor::lt, x, y, 1);
        test!(MPCExecutor::lt, y, x, 0);
    }

    #[test]
    fn gt_public_public() {
        let x = Value::Public(3);
        let y = Value::Public(5);
        test!(MPCExecutor::gt, x, y, 0);
        test!(MPCExecutor::gt, y, x, 1);
    }

    #[test]
    fn gt_public_secret() {
        let x = Value::Public(3);
        let y = Value::Secret(Share::Arithmetic(5));
        test!(MPCExecutor::gt, x, y, 0);
        test!(MPCExecutor::gt, y, x, 1);
    }

    #[test]
    fn gt_secret_secret() {
        let x = Value::Secret(Share::Arithmetic(3));
        let y = Value::Secret(Share::Arithmetic(5));
        test!(MPCExecutor::gt, x, y, 0);
        test!(MPCExecutor::gt, y, x, 1);
    }

    #[test]
    fn le_public_public() {
        let x = Value::Public(3);
        let y = Value::Public(5);
        test!(MPCExecutor::le, x, y, 1);
        test!(MPCExecutor::le, y, x, 0);
        let x = Value::Public(5);
        let y = Value::Public(5);
        test!(MPCExecutor::le, x, y, 1);
    }

    #[test]
    fn le_public_secret() {
        let x = Value::Public(3);
        let y = Value::Secret(Share::Arithmetic(5));
        test!(MPCExecutor::le, x, y, 1);
        test!(MPCExecutor::le, y, x, 0);
        let x = Value::Public(5);
        let y = Value::Secret(Share::Arithmetic(5));
        test!(MPCExecutor::le, x, y, 1);
    }

    #[test]
    fn le_secret_secret() {
        let x = Value::Secret(Share::Arithmetic(3));
        let y = Value::Secret(Share::Arithmetic(5));
        test!(MPCExecutor::le, x, y, 1);
        test!(MPCExecutor::le, y, x, 0);
        let x = Value::Secret(Share::Arithmetic(5));
        let y = Value::Secret(Share::Arithmetic(5));
        test!(MPCExecutor::le, x, y, 1);
    }

    #[test]
    fn ge_public_public() {
        let x = Value::Public(3);
        let y = Value::Public(5);
        test!(MPCExecutor::ge, x, y, 0);
        test!(MPCExecutor::ge, y, x, 1);
        let x = Value::Public(5);
        let y = Value::Public(5);
        test!(MPCExecutor::ge, x, y, 1);
    }

    #[test]
    fn ge_public_secret() {
        let x = Value::Public(3);
        let y = Value::Secret(Share::Arithmetic(5));
        test!(MPCExecutor::ge, x, y, 0);
        test!(MPCExecutor::ge, y, x, 1);
        let x = Value::Public(5);
        let y = Value::Secret(Share::Arithmetic(5));
        test!(MPCExecutor::ge, x, y, 1);
    }

    #[test]
    fn ge_secret_secret() {
        let x = Value::Secret(Share::Arithmetic(3));
        let y = Value::Secret(Share::Arithmetic(5));
        test!(MPCExecutor::ge, x, y, 0);
        test!(MPCExecutor::ge, y, x, 1);
        let x = Value::Secret(Share::Arithmetic(5));
        let y = Value::Secret(Share::Arithmetic(5));
        test!(MPCExecutor::ge, x, y, 1);
    }

    #[test]
    fn eq_public_public() {
        let x = Value::Public(3);
        let y = Value::Public(5);
        test!(MPCExecutor::eq, x, y, 0);
        let x = Value::Public(5);
        let y = Value::Public(5);
        test!(MPCExecutor::eq, x, y, 1);
    }

    #[test]
    fn eq_public_secret() {
        let x = Value::Public(3);
        let y = Value::Secret(Share::Arithmetic(5));
        test!(MPCExecutor::eq, x, y, 0);
        let x = Value::Public(5);
        let y = Value::Secret(Share::Arithmetic(5));
        test!(MPCExecutor::eq, x, y, 1);
    }

    #[test]
    fn eq_secret_secret() {
        let x = Value::Secret(Share::Arithmetic(3));
        let y = Value::Secret(Share::Arithmetic(5));
        test!(MPCExecutor::eq, x, y, 0);
        let x = Value::Secret(Share::Arithmetic(5));
        let y = Value::Secret(Share::Arithmetic(5));
        test!(MPCExecutor::eq, x, y, 1);
    }

    #[test]
    fn neq_public_public() {
        let x = Value::Public(3);
        let y = Value::Public(5);
        test!(MPCExecutor::neq, x, y, 1);
        let x = Value::Public(5);
        let y = Value::Public(5);
        test!(MPCExecutor::neq, x, y, 0);
    }

    #[test]
    fn neq_public_secret() {
        let x = Value::Public(3);
        let y = Value::Secret(Share::Arithmetic(5));
        test!(MPCExecutor::neq, x, y, 1);
        let x = Value::Public(5);
        let y = Value::Secret(Share::Arithmetic(5));
        test!(MPCExecutor::neq, x, y, 0);
    }

    #[test]
    fn neq_secret_secret() {
        let x = Value::Secret(Share::Arithmetic(3));
        let y = Value::Secret(Share::Arithmetic(5));
        test!(MPCExecutor::neq, x, y, 1);
        let x = Value::Secret(Share::Arithmetic(5));
        let y = Value::Secret(Share::Arithmetic(5));
        test!(MPCExecutor::neq, x, y, 0);
    }

    #[test]
    fn a2b() {
        let x = Value::Secret(Share::Arithmetic(42));
        test!(MPCExecutor::a2b, x, 42)
    }

    #[test]
    fn b2a() {
        let x = Value::Secret(Share::Binary(42));
        test!(MPCExecutor::b2a, x, 42)
    }
}

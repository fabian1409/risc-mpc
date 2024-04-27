//! Implementation of the Chou-Orlandi oblivious transfer protocol (cf.
//! <https://eprint.iacr.org/2015/267>).
//!
//! This implementation uses the Ristretto prime order elliptic curve group from
//! the `curve25519-dalek` library and works over blocks rather than arbitrary
//! length messages.
//!
//! This version fixes a bug in the current ePrint write-up
//! (<https://eprint.iacr.org/2015/267/20180529:135402>, Page 4): if the value
//! `x^i` produced by the receiver is not randomized, all the random-OTs
//! produced by the protocol will be the same. We fix this by hashing in `i`
//! during the key derivation phase.

use crate::{channel::Channel, channel::Message, error::Result};
use blake2::{digest::consts::U16, Blake2b, Digest};
use curve25519_dalek::{
    constants::RISTRETTO_BASEPOINT_TABLE,
    ristretto::{RistrettoBasepointTable, RistrettoPoint},
    scalar::Scalar,
};
use rand::{CryptoRng, Rng};
// use scuttlebutt::{AbstractChannel, Block, Malicious, SemiHonest};

type Blake2b128 = Blake2b<U16>;

pub type Block = u128;

/// Oblivious transfer sender.
pub struct OTSender {
    y: Scalar,
    s: RistrettoPoint,
    counter: u128,
}

impl OTSender {
    fn init<C: Channel, RNG: CryptoRng + Rng>(channel: &mut C, mut rng: &mut RNG) -> Result<Self> {
        let y = Scalar::random(&mut rng);
        let s = &y * RISTRETTO_BASEPOINT_TABLE;
        channel.send(Message::Point(s))?;
        Ok(Self { y, s, counter: 0 })
    }

    fn send<C: Channel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        inputs: &[(Block, Block)],
        _: &mut RNG,
    ) -> Result<()> {
        let ys = self.y * self.s;
        let ks = (0..inputs.len())
            .map(|i| {
                let r = channel.recv()?.as_point().unwrap();
                let yr = self.y * r;
                let k0 = hash(self.counter + i as u128, &yr);
                let k1 = hash(self.counter + i as u128, &(yr - ys));
                Ok((k0, k1))
            })
            .collect::<Result<Vec<(Block, Block)>>>()?;
        self.counter += inputs.len() as u128;
        for (input, k) in inputs.iter().zip(ks.into_iter()) {
            let c0 = k.0 ^ input.0;
            let c1 = k.1 ^ input.1;
            channel.send(Message::Block(c0))?;
            channel.send(Message::Block(c1))?;
        }
        Ok(())
    }
}

/// Oblivious transfer receiver.
pub struct OTReceiver {
    s: RistrettoBasepointTable,
    counter: u128,
}

impl OTReceiver {
    fn init<C: Channel, RNG: CryptoRng + Rng>(channel: &mut C, _: &mut RNG) -> Result<Self> {
        let s = channel.recv()?.as_point().unwrap();
        let s = RistrettoBasepointTable::create(&s);
        Ok(Self { s, counter: 0 })
    }

    fn receive<C: Channel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        choices: &[bool],
        mut rng: &mut RNG,
    ) -> Result<Vec<Block>> {
        let zero = &Scalar::ZERO * &self.s;
        let one = &Scalar::ONE * &self.s;
        let ks = choices
            .iter()
            .enumerate()
            .map(|(i, b)| {
                let x = Scalar::random(&mut rng);
                let c = if *b { one } else { zero };
                let r = c + &x * RISTRETTO_BASEPOINT_TABLE;
                channel.send(Message::Point(r))?;
                Ok(hash(self.counter + i as u128, &(&x * &self.s)))
            })
            .collect::<Result<Vec<Block>>>()?;
        self.counter += choices.len() as u128;
        choices
            .iter()
            .zip(ks.into_iter())
            .map(|(b, k)| {
                let c0 = channel.recv()?.as_block().unwrap();
                let c1 = channel.recv()?.as_block().unwrap();
                let c = k ^ if *b { c1 } else { c0 };
                Ok(c)
            })
            .collect()
    }
}

#[inline]
fn hash(seed: u128, pt: &RistrettoPoint) -> Block {
    let mut hasher = Blake2b128::new();
    hasher.update(pt.compress().as_bytes());
    hasher.update(seed.to_le_bytes());
    let digest = hasher.finalize();
    Block::from_le_bytes(digest.into())
}

#[cfg(test)]
mod tests {
    use super::{OTReceiver, OTSender};
    use crate::{channel::Message, co_ot::Block, ThreadChannel};
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

    #[test]
    fn test_co_ot() {
        let (mut ch0, mut ch1) = create_channels();
        let inputs = [(42, 12), (3, 5)];
        let choices = [true, false];
        let chosen = inputs
            .iter()
            .zip(choices.iter())
            .map(|((m0, m1), c)| if *c { m1 } else { m0 })
            .cloned()
            .collect::<Vec<Block>>();

        let sender = thread::spawn(move || {
            let mut rng = rand::thread_rng();
            let mut sender = OTSender::init(&mut ch0, &mut rng).unwrap();
            sender.send(&mut ch0, &inputs, &mut rng).unwrap();
        });
        let receiver = thread::spawn(move || -> Vec<Block> {
            let mut rng = rand::thread_rng();
            let mut receiver = OTReceiver::init(&mut ch1, &mut rng).unwrap();
            receiver.receive(&mut ch1, &choices, &mut rng).unwrap()
        });

        sender.join().unwrap();
        let received = receiver.join().unwrap();
        println!("received = {received:?}");
        assert_eq!(received, chosen);
    }
}

//! Implementation of the Naor-Pinkas oblivious transfer protocol (cf. <https://dl.acm.org/citation.cfm?id=365502>).
//! Based on <https://github.com/GaloisInc/swanky/blob/master/ocelot/src/ot/naor_pinkas.rs>.

#![allow(unused)]

use super::utils::block::{hash_pt, Block};
use crate::{
    channel::{Channel, Message},
    error::{Error, Result},
};
use curve25519_dalek::{
    constants::RISTRETTO_BASEPOINT_TABLE, ristretto::RistrettoPoint, scalar::Scalar,
};
use rand::rngs::ThreadRng;

/// Oblivious transfer sender.
#[derive(Debug)]
pub struct OTSender {
    rng: ThreadRng,
}

impl OTSender {
    /// Create new [`OTReceiver`]
    pub fn new<C: Channel>(_: &mut C) -> Result<OTSender> {
        Ok(OTSender {
            rng: rand::thread_rng(),
        })
    }

    /// Send `inputs` to [`OTReceiver`] using oblivious transfer.
    pub fn send<C: Channel>(&mut self, ch: &mut C, inputs: &[(Block, Block)]) -> Result<()> {
        let m = inputs.len();
        let mut cs = Vec::with_capacity(m);
        let mut pks = Vec::with_capacity(m);
        for _ in 0..m {
            let c = RistrettoPoint::random(&mut self.rng);
            ch.send(Message::Point(c))?;
            cs.push(c);
        }
        for c in cs.into_iter() {
            let pk0 = ch.recv()?.as_point().ok_or(Error::UnexpectedMessage)?;
            pks.push((pk0, c - pk0));
        }
        for (i, (input, pk)) in inputs.iter().zip(pks.into_iter()).enumerate() {
            let r = Scalar::random(&mut self.rng);
            let ei0 = &r * RISTRETTO_BASEPOINT_TABLE;
            let h = hash_pt(i as u128, &(pk.0 * r));
            let e01 = h ^ input.0;
            let h = hash_pt(i as u128, &(pk.1 * r));
            let e11 = h ^ input.1;
            ch.send(Message::Point(ei0))?;
            ch.send(Message::Block(e01))?;
            ch.send(Message::Block(e11))?;
        }
        Ok(())
    }
}

/// Oblivious transfer receiver.
#[derive(Debug)]
pub struct OTReceiver {
    rng: ThreadRng,
}

impl OTReceiver {
    /// Create new [`OTReceiver`]
    pub fn new<C: Channel>(_: &mut C) -> Result<OTReceiver> {
        Ok(OTReceiver {
            rng: rand::thread_rng(),
        })
    }

    /// Receive from [`OTSender`] with the given `inputs` as choice bits.
    pub fn receive<C: Channel>(&mut self, ch: &mut C, inputs: &[bool]) -> Result<Vec<Block>> {
        let m = inputs.len();
        let mut cs = Vec::with_capacity(m);
        let mut ks = Vec::with_capacity(m);
        for _ in 0..m {
            let c = ch.recv()?.as_point().ok_or(Error::UnexpectedMessage)?;
            cs.push(c);
        }
        for (b, c) in inputs.iter().zip(cs.into_iter()) {
            let k = Scalar::random(&mut self.rng);
            let pk = &k * RISTRETTO_BASEPOINT_TABLE;
            let pk_ = c - pk;
            match b {
                false => ch.send(Message::Point(pk))?,
                true => ch.send(Message::Point(pk_))?,
            };
            ks.push(k);
        }
        inputs
            .iter()
            .zip(ks)
            .enumerate()
            .map(|(i, (b, k))| {
                let ei0 = ch.recv()?.as_point().ok_or(Error::UnexpectedMessage)?;
                let e01 = ch.recv()?.as_block().ok_or(Error::UnexpectedMessage)?;
                let e11 = ch.recv()?.as_block().ok_or(Error::UnexpectedMessage)?;
                let e1 = match b {
                    false => e01,
                    true => e11,
                };
                let h = hash_pt(i as u128, &(ei0 * k));
                Ok(h ^ e1)
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::{OTReceiver, OTSender};
    use crate::{channel::Message, ot::utils::block::Block, ThreadChannel};
    use rand::random;
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
    fn test_naor_pinkas() {
        let (mut ch0, mut ch1) = create_channels();
        let n = 100;
        let inputs = (0..n)
            .map(|_| (random(), random()))
            .collect::<Vec<(Block, Block)>>();
        let choices = (0..n).map(|_| random()).collect::<Vec<bool>>();
        let chosen = inputs
            .iter()
            .zip(choices.iter())
            .map(|((m0, m1), c)| if *c { m1 } else { m0 })
            .cloned()
            .collect::<Vec<Block>>();

        let sender = thread::spawn(move || {
            let mut sender = OTSender::new(&mut ch0).unwrap();
            sender.send(&mut ch0, &inputs).unwrap();
        });
        let receiver = thread::spawn(move || -> Vec<Block> {
            let mut receiver = OTReceiver::new(&mut ch1).unwrap();
            receiver.receive(&mut ch1, &choices).unwrap()
        });

        sender.join().unwrap();
        let received = receiver.join().unwrap();
        assert_eq!(received, chosen);
    }
}

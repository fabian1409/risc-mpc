//! Implementation of the Chou-Orlandi oblivious transfer protocol (cf. <https://eprint.iacr.org/2015/267>).
//! Based on <https://github.com/GaloisInc/swanky/blob/master/ocelot/src/ot/chou_orlandi.rs>.

use super::utils::block::{hash_pt, Block};
use crate::{channel::Channel, error::Result};
use curve25519_dalek::{
    constants::RISTRETTO_BASEPOINT_TABLE,
    ristretto::{RistrettoBasepointTable, RistrettoPoint},
    scalar::Scalar,
};
use rand::rngs::ThreadRng;
use std::fmt;

/// Oblivious transfer sender.
#[derive(Debug)]
pub struct OTSender {
    y: Scalar,
    s: RistrettoPoint,
    counter: u128,
}

impl OTSender {
    /// Create new [`OTSender`]
    pub fn new<C: Channel>(ch: &mut C) -> Result<Self> {
        let mut rng = rand::thread_rng();
        let y = Scalar::random(&mut rng);
        let s = &y * RISTRETTO_BASEPOINT_TABLE;
        ch.send_point(&s)?;
        Ok(Self { y, s, counter: 0 })
    }

    /// Send `inputs` to [`OTReceiver`] using oblivious transfer.
    pub fn send<C: Channel>(&mut self, ch: &mut C, inputs: &[(Block, Block)]) -> Result<()> {
        let ys = self.y * self.s;
        let ks = (0..inputs.len())
            .map(|i| {
                let r = ch.recv_point()?;
                let yr = self.y * r;
                let k0 = hash_pt(self.counter + i as u128, &yr);
                let k1 = hash_pt(self.counter + i as u128, &(yr - ys));
                Ok((k0, k1))
            })
            .collect::<Result<Vec<(Block, Block)>>>()?;
        self.counter += inputs.len() as u128;
        for (input, k) in inputs.iter().zip(ks.into_iter()) {
            let c0 = k.0 ^ input.0;
            let c1 = k.1 ^ input.1;
            ch.send_block(c0)?;
            ch.send_block(c1)?;
        }
        Ok(())
    }
}

/// Oblivious transfer receiver.
pub struct OTReceiver {
    s: RistrettoBasepointTable,
    counter: u128,
    rng: ThreadRng,
}

impl OTReceiver {
    /// Create new [`OTReceiver`]
    pub fn new<C: Channel>(ch: &mut C) -> Result<Self> {
        let s = ch.recv_point()?;
        let s = RistrettoBasepointTable::create(&s);
        Ok(Self {
            s,
            counter: 0,
            rng: rand::thread_rng(),
        })
    }

    /// Receive from [`OTSender`] with the given `inputs` as choice bits.
    pub fn receive<C: Channel>(&mut self, ch: &mut C, choices: &[bool]) -> Result<Vec<Block>> {
        let zero = &Scalar::ZERO * &self.s;
        let one = &Scalar::ONE * &self.s;
        let ks = choices
            .iter()
            .enumerate()
            .map(|(i, b)| {
                let x = Scalar::random(&mut self.rng);
                let c = if *b { one } else { zero };
                let r = c + &x * RISTRETTO_BASEPOINT_TABLE;
                ch.send_point(&r)?;
                Ok(hash_pt(self.counter + i as u128, &(&x * &self.s)))
            })
            .collect::<Result<Vec<Block>>>()?;
        self.counter += choices.len() as u128;
        choices
            .iter()
            .zip(ks)
            .map(|(b, k)| {
                let c0 = ch.recv_block()?;
                let c1 = ch.recv_block()?;
                let c = k ^ if *b { c1 } else { c0 };
                Ok(c)
            })
            .collect()
    }
}

impl fmt::Debug for OTReceiver {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("OTReceiver")
            .field("counter", &self.counter)
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::{OTReceiver, OTSender};
    use crate::{ot::utils::block::Block, ThreadChannel};
    use bytes::Bytes;
    use rand::random;
    use std::{
        sync::mpsc::{self, Receiver, Sender},
        thread,
        time::Instant,
    };

    fn create_channels() -> (ThreadChannel, ThreadChannel) {
        let (tx0, rx0): (Sender<Bytes>, Receiver<Bytes>) = mpsc::channel();
        let (tx1, rx1): (Sender<Bytes>, Receiver<Bytes>) = mpsc::channel();
        let ch0 = ThreadChannel::new(tx0, rx1);
        let ch1 = ThreadChannel::new(tx1, rx0);
        (ch0, ch1)
    }

    #[test]
    fn test_chou_orlandi() {
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
            let start = Instant::now();
            sender.send(&mut ch0, &inputs).unwrap();
            println!("send took {}ms", start.elapsed().as_millis())
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

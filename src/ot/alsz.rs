//! Implementation of the Asharov-Lindell-Schneider-Zohner oblivious transfer extension protocol (cf. <https://eprint.iacr.org/2016/602>, Protocol 4).
//! Based on <https://github.com/GaloisInc/swanky/blob/dev/ocelot/src/ot/alsz.rs>.

use super::{
    chou_orlandi::{OTReceiver, OTSender},
    utils::{
        aes_hash::{AesHash, FIXED_KEY},
        aes_rng::AesRng,
        block::Block,
        boolvec_to_u8vec, transpose, u8vec_to_boolvec, xor_inplace,
    },
};
use crate::{
    channel::{Channel, Message},
    error::{Error, Result},
};
use rand::Rng;
use rand_core::{RngCore, SeedableRng};

const NUM_BASE_OT: usize = 128;

/// Oblivious transfer sender.
#[derive(Debug)]
pub struct OTExtSender {
    s: Vec<bool>,
    s_: Block,
    rngs: Vec<AesRng>,
    hash: AesHash,
}

impl OTExtSender {
    pub fn new<C: Channel>(channel: &mut C) -> Result<Self> {
        let mut s_ = [0u8; 16];
        let mut rng = rand::thread_rng();
        rng.fill_bytes(&mut s_);
        let mut base_receiver = OTReceiver::new(channel)?;
        let s = u8vec_to_boolvec(&s_);
        let ks = base_receiver.receive(channel, &s)?;
        let rngs = ks
            .into_iter()
            .map(|k| AesRng::from_seed(k.to_le_bytes()))
            .collect::<Vec<AesRng>>();
        Ok(Self {
            s,
            s_: Block::from_le_bytes(s_),
            rngs,
            hash: AesHash::new(&FIXED_KEY.to_le_bytes().into()),
        })
    }

    fn send_setup<C: Channel>(&mut self, channel: &mut C, m: usize) -> Result<Vec<u8>> {
        const NROWS: usize = NUM_BASE_OT;
        let ncols = if m % 8 != 0 { m + (8 - m % 8) } else { m };
        let mut qs = vec![0u8; NROWS * ncols / 8];
        let mut u = vec![0u8; ncols / 8];
        let zero = vec![0u8; ncols / 8];
        for (j, (b, rng)) in self.s.iter().zip(self.rngs.iter_mut()).enumerate() {
            let range = j * ncols / 8..(j + 1) * ncols / 8;
            let q = &mut qs[range];
            u.copy_from_slice(channel.recv()?.as_bytes().ok_or(Error::UnexpectedMessage)?);
            rng.fill_bytes(q);
            xor_inplace(q, if *b { &u } else { &zero });
        }
        Ok(transpose(&qs, NROWS, ncols))
    }

    pub fn send<C: Channel>(&mut self, channel: &mut C, inputs: &[(Block, Block)]) -> Result<()> {
        let m = inputs.len();
        let qs = self.send_setup(channel, m)?;
        for (j, input) in inputs.iter().enumerate() {
            let q = &qs[j * 16..(j + 1) * 16];
            let q: [u8; 16] = q.try_into().unwrap();
            let q = Block::from_le_bytes(q);
            let y0 = self.hash.cr_hash(q) ^ input.0;
            let q = q ^ self.s_;
            let y1 = self.hash.cr_hash(q) ^ input.1;
            channel.send(Message::Block(y0))?;
            channel.send(Message::Block(y1))?;
        }
        Ok(())
    }

    pub fn send_correlated<C: Channel>(
        &mut self,
        channel: &mut C,
        deltas: &[Block],
    ) -> Result<Vec<(Block, Block)>> {
        let m = deltas.len();
        let qs = self.send_setup(channel, m)?;
        let mut out = Vec::with_capacity(m);
        for (j, delta) in deltas.iter().enumerate() {
            let q = &qs[j * 16..(j + 1) * 16];
            let q: [u8; 16] = q.try_into().unwrap();
            let q = Block::from_le_bytes(q);
            let x0 = self.hash.cr_hash(q);
            let x1 = x0 ^ *delta;
            let q = q ^ self.s_;
            let y = self.hash.cr_hash(q) ^ x1;
            channel.send(Message::Block(y))?;
            out.push((x0, x1));
        }
        Ok(out)
    }

    pub fn send_random<C: Channel>(
        &mut self,
        channel: &mut C,
        m: usize,
    ) -> Result<Vec<(Block, Block)>> {
        let qs = self.send_setup(channel, m)?;
        let mut out = Vec::with_capacity(m);
        for j in 0..m {
            let q = &qs[j * 16..(j + 1) * 16];
            let q: [u8; 16] = q.try_into().unwrap();
            let q = Block::from_le_bytes(q);
            let x0 = self.hash.cr_hash(q);
            let q = q ^ self.s_;
            let x1 = self.hash.cr_hash(q);
            out.push((x0, x1));
        }
        Ok(out)
    }
}

/// Oblivious transfer receiver.
#[derive(Debug)]
pub struct OTExtReceiver {
    rngs: Vec<(AesRng, AesRng)>,
    hash: AesHash,
}

impl OTExtReceiver {
    pub fn new<C: Channel>(channel: &mut C) -> Result<Self> {
        let mut base_sender = OTSender::new(channel)?;
        let mut rng = rand::thread_rng();
        let mut ks = Vec::with_capacity(NUM_BASE_OT);
        for _ in 0..NUM_BASE_OT {
            let k0 = rng.gen();
            let k1 = rng.gen();
            ks.push((k0, k1));
        }
        base_sender.send(channel, &ks)?;
        let rngs = ks
            .into_iter()
            .map(|(k0, k1)| {
                (
                    AesRng::from_seed(k0.to_le_bytes()),
                    AesRng::from_seed(k1.to_le_bytes()),
                )
            })
            .collect::<Vec<(AesRng, AesRng)>>();
        Ok(Self {
            rngs,
            hash: AesHash::new(&FIXED_KEY.to_le_bytes().into()),
        })
    }

    fn receive_setup<C: Channel>(
        &mut self,
        channel: &mut C,
        r: &[u8],
        m: usize,
    ) -> Result<Vec<u8>> {
        const NROWS: usize = 128;
        let ncols = if m % 8 != 0 { m + (8 - m % 8) } else { m };
        let mut ts = vec![0u8; NROWS * ncols / 8];
        let mut g = vec![0u8; ncols / 8];
        for j in 0..self.rngs.len() {
            let range = j * ncols / 8..(j + 1) * ncols / 8;
            let t = &mut ts[range];
            self.rngs[j].0.fill_bytes(t);
            self.rngs[j].1.fill_bytes(&mut g);
            xor_inplace(&mut g, t);
            xor_inplace(&mut g, r);
            channel.send(Message::Bytes(g.clone()))?;
        }
        Ok(transpose(&ts, NROWS, ncols))
    }

    pub fn receive<C: Channel>(&mut self, channel: &mut C, inputs: &[bool]) -> Result<Vec<Block>> {
        let r = boolvec_to_u8vec(inputs);
        let ts = self.receive_setup(channel, &r, inputs.len())?;
        let mut out = Vec::with_capacity(inputs.len());
        for (j, b) in inputs.iter().enumerate() {
            let t = &ts[j * 16..(j + 1) * 16];
            let t: [u8; 16] = t.try_into().unwrap();
            let y0 = channel.recv()?.as_block().ok_or(Error::UnexpectedMessage)?;
            let y1 = channel.recv()?.as_block().ok_or(Error::UnexpectedMessage)?;
            let y = if *b { y1 } else { y0 };
            let y = y ^ self.hash.cr_hash(Block::from_le_bytes(t));
            out.push(y);
        }
        Ok(out)
    }

    pub fn receive_correlated<C: Channel>(
        &mut self,
        channel: &mut C,
        inputs: &[bool],
    ) -> Result<Vec<Block>> {
        let r = boolvec_to_u8vec(inputs);
        let ts = self.receive_setup(channel, &r, inputs.len())?;
        let mut out = Vec::with_capacity(inputs.len());
        for (j, b) in inputs.iter().enumerate() {
            let t = &ts[j * 16..(j + 1) * 16];
            let t: [u8; 16] = t.try_into().unwrap();
            let y = channel.recv()?.as_block().ok_or(Error::UnexpectedMessage)?;
            let y = if *b { y } else { Block::default() };
            let h = self.hash.cr_hash(Block::from_le_bytes(t));
            out.push(y ^ h);
        }
        Ok(out)
    }

    pub fn receive_random<C: Channel>(
        &mut self,
        channel: &mut C,
        inputs: &[bool],
    ) -> Result<Vec<Block>> {
        let r = boolvec_to_u8vec(inputs);
        let ts = self.receive_setup(channel, &r, inputs.len())?;
        let mut out = Vec::with_capacity(inputs.len());
        for j in 0..inputs.len() {
            let t = &ts[j * 16..(j + 1) * 16];
            let t: [u8; 16] = t.try_into().unwrap();
            let h = self.hash.cr_hash(Block::from_be_bytes(t));
            out.push(h);
        }
        Ok(out)
    }
}

#[cfg(test)]
mod tests {
    use super::{OTExtReceiver, OTExtSender};
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
    fn test_alsz() {
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
            let mut sender = OTExtSender::new(&mut ch0).unwrap();
            sender.send(&mut ch0, &inputs).unwrap();
        });
        let receiver = thread::spawn(move || -> Vec<Block> {
            let mut receiver = OTExtReceiver::new(&mut ch1).unwrap();
            receiver.receive(&mut ch1, &choices).unwrap()
        });

        sender.join().unwrap();
        let received = receiver.join().unwrap();
        assert_eq!(received, chosen);
    }
}

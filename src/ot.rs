// https://github.com/GaloisInc/swanky/blob/master/ocelot/src/ot/naor_pinkas.rs

use crate::{channel::Channel, channel::Message, error::Result};
use rug::{integer::Order, rand::RandState, Integer};
use sha3::{Digest, Sha3_512};

// http://www.herongyang.com/Cryptography/DSA-Java-Example-of-DSA-Key-Parameters-Properties.html
/// Group generator
const G: &str = "5421644057436475141609648488325705128047428394380474376834667300766108262613900542681289080713724597310673074119355136085795982097390670890367185141189796";
/// Prime modulus
const P: &str = "13232376895198612407547930718267435757728527029623408872245156039757713029036368719146452186041204237350521785240337048752071462798273003935646236777459223";

/// Oblivious transfer sender.
pub struct OTSender {
    g: Integer,
    p: Integer,
}
/// Oblivious transfer receiver.
pub struct OTReceiver {
    g: Integer,
    p: Integer,
}

impl OTSender {
    pub fn new() -> OTSender {
        OTSender {
            g: G.parse().unwrap(),
            p: P.parse().unwrap(),
        }
    }

    /// Send `inputs` to [`OTReceiver`] using oblivious transfer.
    pub fn send<T: Channel>(
        &mut self,
        channel: &mut T,
        inputs: &[(Integer, Integer)],
    ) -> Result<()> {
        let mut rng = RandState::new();
        let m = inputs.len();
        let mut cs = Vec::with_capacity(m);
        let mut pks = Vec::with_capacity(m);
        for _ in 0..m {
            let c = Integer::from(Integer::random_bits(256, &mut rng));
            channel.send(Message::Integer(c.clone()))?;
            cs.push(c);
        }
        for c in cs {
            let pk0 = channel.recv()?.as_int().unwrap();
            pks.push((
                pk0.clone(),
                (c * pk0.invert(&self.p).unwrap()) % self.p.clone(),
            ));
        }
        for (input, pk) in inputs.iter().zip(pks.into_iter()) {
            let r = Integer::from(Integer::random_bits(256, &mut rng));
            let ei0 = Integer::from(self.g.pow_mod_ref(&r, &self.p).unwrap());
            let h = hash(&pk.0.pow_mod(&r, &self.p).unwrap());
            let e01 = h ^ input.0.clone();
            let h = hash(&pk.1.pow_mod(&r, &self.p).unwrap());
            let e11 = h ^ input.1.clone();
            channel.send(Message::Integer(ei0))?;
            channel.send(Message::Integer(e01))?;
            channel.send(Message::Integer(e11))?;
        }
        Ok(())
    }
}

impl OTReceiver {
    pub fn new() -> OTReceiver {
        OTReceiver {
            g: G.parse().unwrap(),
            p: P.parse().unwrap(),
        }
    }

    /// Receive from [`OTSender`] with the given `inputs` as choice bits.
    pub fn receive<T: Channel>(
        &mut self,
        channel: &mut T,
        inputs: &[bool],
    ) -> Result<Vec<Integer>> {
        let mut rng = RandState::new();
        let m = inputs.len();
        let mut cs = Vec::with_capacity(m);
        let mut ks = Vec::with_capacity(m);
        for _ in 0..m {
            let c = channel.recv()?.as_int().unwrap();
            cs.push(c);
        }
        for (b, c) in inputs.iter().zip(cs) {
            let k = Integer::from(Integer::random_bits(256, &mut rng));
            let pk = Integer::from(self.g.pow_mod_ref(&k, &self.p).unwrap());
            let pk_ = (c * Integer::from(pk.invert_ref(&self.p).unwrap())) % self.p.clone();
            match b {
                false => channel.send(Message::Integer(pk))?,
                true => channel.send(Message::Integer(pk_))?,
            };
            ks.push(k);
        }
        inputs
            .iter()
            .zip(ks)
            .map(|(b, k)| {
                let ei0 = channel.recv()?.as_int().unwrap();
                let e01 = channel.recv()?.as_int().unwrap();
                let e11 = channel.recv()?.as_int().unwrap();
                let e1 = match b {
                    false => e01,
                    true => e11,
                };
                let h = hash(&ei0.pow_mod(&k, &self.p).unwrap());
                Ok(h ^ e1)
            })
            .collect()
    }
}

fn hash(x: &Integer) -> Integer {
    let digest = Sha3_512::digest(x.to_digits(Order::Msf));
    Integer::from_digits(digest.as_slice(), Order::Msf)
}

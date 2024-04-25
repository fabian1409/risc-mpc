use crate::{
    error::Result,
    ot::block::Block,
    party::{Location, PARTY_0},
    Share,
};
use curve25519_dalek::RistrettoPoint;
#[cfg(test)]
use mockall::*;
use serde::{Deserialize, Serialize};
use std::{
    net::SocketAddr,
    sync::mpsc::{Receiver, Sender},
    time::Duration,
};
use tsyncp::channel::{channel_on, channel_to, BincodeChannel};

/// [`Message`] used by [`Channel`].
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Message {
    Share(Share),
    SecretInputs(Vec<(Location, Share)>),
    Point(RistrettoPoint),
    Block(Block),
}

impl Message {
    pub fn as_share(&self) -> Option<Share> {
        match self {
            Message::Share(share) => Some(*share),
            _ => None,
        }
    }

    pub fn as_point(&self) -> Option<RistrettoPoint> {
        match self {
            Message::Point(point) => Some(*point),
            _ => None,
        }
    }

    pub fn as_block(&self) -> Option<Block> {
        match self {
            Message::Block(block) => Some(*block),
            _ => None,
        }
    }
}

/// [`Channel`] trait for communication between parties.
#[cfg_attr(test, automock)]
pub trait Channel {
    fn send(&mut self, msg: Message) -> Result<()>;
    fn recv(&mut self) -> Result<Message>;
}

/// [`ThreadChannel`] for communication between threads.
#[derive(Debug)]
pub struct ThreadChannel {
    tx: Sender<Message>,
    rx: Receiver<Message>,
}

impl ThreadChannel {
    pub fn new(tx: Sender<Message>, rx: Receiver<Message>) -> Self {
        ThreadChannel { tx, rx }
    }
}

impl Channel for ThreadChannel {
    fn send(&mut self, msg: Message) -> Result<()> {
        Ok(self.tx.send(msg).map_err(Box::from)?)
    }

    fn recv(&mut self) -> Result<Message> {
        Ok(self.rx.recv().map_err(Box::from)?)
    }
}

/// [`TcpChannel`] for communication via a TCP connection.
#[derive(Debug)]
pub struct TcpChannel {
    ch: BincodeChannel<Message>,
}

impl TcpChannel {
    /// Create a new [`TcpChannel`] for the party with `id`.
    /// Connect to other party with given [`SocketAddr`].
    pub fn new(id: usize, addr: SocketAddr) -> Result<TcpChannel> {
        let ch: BincodeChannel<Message> = if id == PARTY_0 {
            smol::block_on(
                channel_on(addr)
                    .retry(Duration::from_millis(500), 100)
                    .set_tcp_reuseaddr(true)
                    .set_tcp_nodelay(true),
            )?
        } else {
            smol::block_on(
                channel_to(addr)
                    .retry(Duration::from_millis(500), 100)
                    .set_tcp_reuseaddr(true)
                    .set_tcp_nodelay(true),
            )?
        };

        Ok(TcpChannel { ch })
    }
}

impl Channel for TcpChannel {
    fn send(&mut self, msg: Message) -> Result<()> {
        Ok(smol::block_on(self.ch.send(msg)).map_err(Box::from)?)
    }

    fn recv(&mut self) -> Result<Message> {
        Ok(smol::block_on(self.ch.recv())
            .expect("received None")
            .map_err(Box::from)?)
    }
}

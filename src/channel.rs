use crate::{
    error::Result,
    ot::utils::block::Block,
    party::{Location, PARTY_0},
    Share,
};
use curve25519_dalek::RistrettoPoint;
use serde::{Deserialize, Serialize};
use std::{
    net::SocketAddr,
    sync::mpsc::{Receiver, Sender},
    time::Duration,
};
use tokio::runtime::Runtime;
use tsyncp::channel::{channel_on, channel_to, BincodeChannel};

/// [`Message`] used by [`Channel`].
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Message {
    Share(Share),
    SecretInputs(Vec<(Location, Share)>),
    Point(RistrettoPoint),
    Block(Block),
    Bytes(Vec<u8>),
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

    pub fn as_bytes(&self) -> Option<&[u8]> {
        match self {
            Message::Bytes(bytes) => Some(bytes),
            _ => None,
        }
    }
}

/// [`Channel`] trait for communication between parties.
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
    rt: Runtime,
}

impl TcpChannel {
    /// Create a new [`TcpChannel`] for the party with `id`.
    /// Connect to other party with given [`SocketAddr`].
    pub fn new(id: usize, addr: SocketAddr) -> Result<TcpChannel> {
        let rt = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .expect("failed to build runtime");

        let ch: BincodeChannel<Message> = if id == PARTY_0 {
            rt.block_on(
                channel_on(addr)
                    .retry(Duration::from_millis(500), 100)
                    .set_tcp_reuseaddr(true)
                    .set_tcp_nodelay(true),
            )?
        } else {
            rt.block_on(
                channel_to(addr)
                    .retry(Duration::from_millis(500), 100)
                    .set_tcp_reuseaddr(true)
                    .set_tcp_nodelay(true),
            )?
        };

        Ok(TcpChannel { ch, rt })
    }
}

impl Channel for TcpChannel {
    fn send(&mut self, msg: Message) -> Result<()> {
        Ok(self.rt.block_on(self.ch.send(msg)).map_err(Box::from)?)
    }

    fn recv(&mut self) -> Result<Message> {
        Ok(self
            .rt
            .block_on(self.ch.recv())
            .expect("received None")
            .map_err(Box::from)?)
    }
}

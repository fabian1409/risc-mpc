use crate::{
    party::{Location, PARTY_0},
    types::Value,
    Share,
};
#[cfg(test)]
use mockall::*;
use rug::Integer;
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
    SecretInputs(Vec<(Location, Value)>),
    Integer(Integer),
}

impl Message {
    pub fn as_share(&self) -> Option<Share> {
        match self {
            Message::Share(share) => Some(*share),
            _ => None,
        }
    }

    pub fn as_int(&self) -> Option<Integer> {
        match self {
            Message::Integer(int) => Some(int.clone()),
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
        Ok(self.tx.send(msg)?)
    }

    fn recv(&mut self) -> Result<Message> {
        Ok(self.rx.recv()?)
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
            .build()?;

        let ch: BincodeChannel<Message> = if id == PARTY_0 {
            rt.block_on(
                channel_on(addr)
                    .retry(Duration::from_millis(500), 100)
                    .set_tcp_reuseaddr(true),
            )?
        } else {
            rt.block_on(
                channel_to(addr)
                    .retry(Duration::from_millis(500), 100)
                    .set_tcp_reuseaddr(true),
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

pub type Result<T> = std::result::Result<T, self::error::Error>;

pub mod error {
    use super::Message;
    use thiserror::Error;

    #[allow(clippy::enum_variant_names)]
    #[derive(Debug, Error)]
    pub enum Error {
        #[error(transparent)]
        SendError(#[from] std::sync::mpsc::SendError<Message>),
        #[error(transparent)]
        RecvError(#[from] std::sync::mpsc::RecvError),
        #[error(transparent)]
        IOError(#[from] std::io::Error),
        #[error(transparent)]
        ChannelBuilderError(#[from] tsyncp::channel::builder::errors::BuilderError),
        #[error(transparent)]
        ChannelError(#[from] Box<dyn std::error::Error + Send + Sync>),
    }
}

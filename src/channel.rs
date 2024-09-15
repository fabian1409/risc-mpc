use crate::{error::Result, ot::utils::block::Block, party::Location, types::Value, Share};
use bytes::Bytes;
use curve25519_dalek::RistrettoPoint;
use futures::{SinkExt, StreamExt};
use std::sync::mpsc::{Receiver, Sender};
use std::{thread, time::Duration};
use tokio::{
    net::{TcpListener, TcpStream, ToSocketAddrs},
    runtime::Runtime,
};
use tokio_util::codec::{Framed, LengthDelimitedCodec};

/// [`Channel`] trait for communication between parties.
pub trait Channel {
    fn send(&mut self, data: Bytes) -> Result<()>;

    fn recv(&mut self) -> Result<Bytes>;

    fn send_share(&mut self, share: Share) -> Result<()> {
        let bytes = bincode::serialize(&share).unwrap();
        self.send(Bytes::from(bytes))
    }

    fn recv_share(&mut self) -> Result<Share> {
        let bytes = self.recv()?;
        Ok(bincode::deserialize(&bytes).unwrap())
    }

    fn send_share2(&mut self, shares: (Share, Share)) -> Result<()> {
        let bytes = bincode::serialize(&shares).unwrap();
        self.send(Bytes::from(bytes))
    }

    fn recv_share2(&mut self) -> Result<(Share, Share)> {
        let bytes = self.recv()?;
        Ok(bincode::deserialize(&bytes).unwrap())
    }

    fn send_share_vec(&mut self, shares: &[Share]) -> Result<()> {
        let bytes = bincode::serialize(shares).unwrap();
        self.send(Bytes::from(bytes))
    }

    fn recv_share_vec(&mut self) -> Result<Vec<Share>> {
        let bytes = self.recv()?;
        Ok(bincode::deserialize(&bytes).unwrap())
    }

    fn send_secret_inputs(&mut self, inputs: &[(Location, Value)]) -> Result<()> {
        let bytes = bincode::serialize(inputs).unwrap();
        self.send(Bytes::from(bytes))
    }

    fn recv_secret_inputs(&mut self) -> Result<Vec<(Location, Value)>> {
        let bytes = self.recv()?;
        Ok(bincode::deserialize(&bytes).unwrap())
    }

    fn send_point(&mut self, point: &RistrettoPoint) -> Result<()> {
        let bytes = bincode::serialize(point).unwrap();
        self.send(Bytes::from(bytes))
    }

    fn recv_point(&mut self) -> Result<RistrettoPoint> {
        let bytes = self.recv()?;
        Ok(bincode::deserialize(&bytes).unwrap())
    }

    fn send_block(&mut self, block: Block) -> Result<()> {
        let bytes = bincode::serialize(&block).unwrap();
        self.send(Bytes::from(bytes))
    }

    fn recv_block(&mut self) -> Result<Block> {
        let bytes = self.recv()?;
        Ok(bincode::deserialize(&bytes).unwrap())
    }
}

/// [`ThreadChannel`] for communication between threads.
#[derive(Debug)]
pub struct ThreadChannel {
    tx: Sender<Bytes>,
    rx: Receiver<Bytes>,
}

impl ThreadChannel {
    pub fn new(tx: Sender<Bytes>, rx: Receiver<Bytes>) -> Self {
        ThreadChannel { tx, rx }
    }
}

impl Channel for ThreadChannel {
    fn send(&mut self, data: Bytes) -> Result<()> {
        self.tx.send(data).expect("can send");
        Ok(())
    }

    fn recv(&mut self) -> Result<Bytes> {
        Ok(self.rx.recv().expect("can recv"))
    }
}

/// [`TcpChannel`] for communication via a TCP connection.
#[derive(Debug)]
pub struct TcpChannel {
    rt: Runtime,
    stream: Framed<TcpStream, LengthDelimitedCodec>,
}

impl TcpChannel {
    /// Create a new [`TcpChannel`] and bind to `addr`.
    pub fn bind<A: ToSocketAddrs>(addr: A) -> Result<TcpChannel> {
        let rt = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .expect("failed to build runtime");

        let listener = rt.block_on(TcpListener::bind(addr))?;
        let (stream, _) = rt.block_on(listener.accept())?;
        let stream = Framed::new(stream, LengthDelimitedCodec::new());
        Ok(Self { rt, stream })
    }

    /// Create a new [`TcpChannel`] and connect to `addr`.
    pub fn connect<A: ToSocketAddrs>(addr: A) -> Result<TcpChannel> {
        let rt = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .expect("failed to build runtime");

        let stream = loop {
            if let Ok(stream) = rt.block_on(TcpStream::connect(&addr)) {
                break stream;
            } else {
                thread::sleep(Duration::from_millis(100));
            }
        };
        let stream = Framed::new(stream, LengthDelimitedCodec::new());
        Ok(Self { rt, stream })
    }
}

impl Channel for TcpChannel {
    fn send(&mut self, data: Bytes) -> Result<()> {
        Ok(self.rt.block_on(self.stream.send(data))?)
    }

    fn recv(&mut self) -> Result<Bytes> {
        let bytes = self.rt.block_on(self.stream.next()).expect("not closed")?;
        Ok(bytes.into())
    }
}

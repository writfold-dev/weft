//! Bounded newline framing over the owned peer's pipes.
//!
//! Both directions obey the pinned 65,536-byte ceiling, LF included. A reply
//! that would exceed the ceiling is a fatal framing violation, never a
//! truncated frame; a reply that never arrives before the deadline fails the
//! request and the caller kills the owned child.

use std::{
    io::{BufRead, BufReader, Write},
    process::{ChildStdin, ChildStdout},
    sync::mpsc::{Receiver, SyncSender, sync_channel},
    thread::{self, JoinHandle},
    time::Duration,
};
use weft_wire::rpc::FRAME_LIMIT;

pub(crate) enum Incoming {
    Frame(Vec<u8>),
    Eof,
    Fault(&'static str),
}
pub(crate) struct Link {
    stdin: Option<ChildStdin>,
    incoming: Receiver<Incoming>,
    reader: Option<JoinHandle<()>>,
}
impl Link {
    /// Wires the pipes and starts the single reader thread. The thread owns
    /// stdout; every error becomes a delivered fault, never a panic.
    pub(crate) fn new(
        stdin: ChildStdin,
        stdout: ChildStdout,
    ) -> Result<(Self, JoinHandle<()>), String> {
        let (sender, receiver) = sync_channel::<Incoming>(16);
        let reader = thread::Builder::new()
            .spawn(move || read_loop(stdout, sender))
            .map_err(|error| format!("cannot start the reader thread: {error}"))?;
        Ok((
            Self {
                stdin: Some(stdin),
                incoming: receiver,
                reader: None,
            },
            reader,
        ))
    }
    pub(crate) fn attach_reader(&mut self, reader: JoinHandle<()>) {
        self.reader = Some(reader);
    }
    /// Writes one LF-terminated frame, refusing to exceed the ceiling.
    pub(crate) fn send(&mut self, frame: &[u8]) -> Result<(), &'static str> {
        if frame.is_empty() || frame.last() != Some(&b'\n') {
            return Err("outgoing frame is not LF terminated");
        }
        if frame.len() > FRAME_LIMIT {
            return Err("outgoing frame exceeds the transport ceiling");
        }
        let stdin = self.stdin.as_mut().ok_or("peer stdin is already closed")?;
        stdin
            .write_all(frame)
            .and_then(|()| stdin.flush())
            .map_err(|_| "cannot write the complete frame to the peer")
    }
    /// Waits for the next complete reply frame until the deadline.
    pub(crate) fn receive(&mut self, timeout: Duration) -> Result<Vec<u8>, String> {
        match self.incoming.recv_timeout(timeout) {
            Ok(Incoming::Frame(frame)) => Ok(frame),
            Ok(Incoming::Eof) => Err("peer closed the connection without a reply".into()),
            Ok(Incoming::Fault(reason)) => Err(format!("peer stream is unusable: {reason}")),
            Err(std::sync::mpsc::RecvTimeoutError::Timeout) => {
                Err("deadline exceeded while waiting for the reply".into())
            }
            Err(std::sync::mpsc::RecvTimeoutError::Disconnected) => {
                Err("reader thread stopped without delivering a reply".into())
            }
        }
    }
    /// Joins the reader thread; valid after the child exited (EOF or kill).
    pub(crate) fn join_reader(&mut self) {
        if let Some(reader) = self.reader.take() {
            let _ = reader.join();
        }
    }
    /// Closes our side; a shut-down peer observes EOF immediately after.
    pub(crate) fn close_stdin(&mut self) {
        self.stdin = None;
    }
}
fn read_loop(stdout: ChildStdout, sender: SyncSender<Incoming>) {
    let mut reader = BufReader::with_capacity(8192, stdout);
    let mut line = Vec::new();
    loop {
        line.clear();
        let incoming = match reader.read_until(b'\n', &mut line) {
            Ok(0) => Incoming::Eof,
            Ok(_) if line.len() > FRAME_LIMIT => {
                Incoming::Fault("reply frame exceeds the transport ceiling")
            }
            Ok(_) if line.last() == Some(&b'\n') => {
                line.truncate(line.len() - 1);
                Incoming::Frame(line.clone())
            }
            Ok(_) => Incoming::Fault("reply frame is not LF terminated"),
            Err(_) => Incoming::Fault("peer stdout read failed"),
        };
        let terminal = matches!(incoming, Incoming::Eof | Incoming::Fault(_));
        if sender.send(incoming).is_err() || terminal {
            return;
        }
    }
}

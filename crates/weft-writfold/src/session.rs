//! The control-session state machine for one owned peer process.
//!
//! Requests are typed: only `initialize` and `shutdown` exist, so unavailable
//! peer services cannot be requested by accident. Correlation, generation and
//! session-label continuity are enforced on every reply; any deviation is a
//! refusal, never a retry against guessed state.

use crate::{
    child::Peer,
    contract::{self, Admission},
    frame::Link,
};
use std::{fmt, time::Duration};
use weft_wire::rpc::{self, InitializeResult, Method, Reply, SessionLabels, ShutdownResult};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ControlError {
    Spawn(String),
    Io(String),
    Deadline,
    Frame(String),
    Protocol(String),
    Identity(String),
    Refused(String),
    Peer {
        code: i64,
        message: String,
        category: Option<String>,
    },
}
impl fmt::Display for ControlError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Spawn(reason)
            | Self::Io(reason)
            | Self::Frame(reason)
            | Self::Protocol(reason)
            | Self::Identity(reason)
            | Self::Refused(reason) => {
                write!(formatter, "{reason}")
            }
            Self::Deadline => write!(formatter, "the peer did not answer before the deadline"),
            Self::Peer {
                code,
                message,
                category,
            } => match category {
                Some(category) => write!(formatter, "peer refusal {code} ({category}): {message}"),
                None => write!(formatter, "peer refusal {code}: {message}"),
            },
        }
    }
}
impl std::error::Error for ControlError {}
impl From<rpc::FrameError> for ControlError {
    fn from(error: rpc::FrameError) -> Self {
        Self::Protocol(error.to_string())
    }
}
/// A fully completed control session: reply observed, EOF seen, child reaped.
pub struct Completed {
    pub shutdown: ShutdownResult,
    pub exit_code: u64,
    pub stderr: Vec<u8>,
}
enum State {
    Uninitialized,
    Initialized(SessionLabels),
    Closed,
}
pub struct Client {
    peer: Peer,
    link: Link,
    state: State,
    sent: u64,
    timeout: Duration,
}
impl Client {
    pub fn spawn(program: &str, argument: &str, timeout: Duration) -> Result<Self, ControlError> {
        let mut peer = Peer::spawn(program, argument).map_err(ControlError::Spawn)?;
        let (stdin, stdout) = peer.parts().map_err(ControlError::Spawn)?;
        let (mut link, reader) = Link::new(stdin, stdout).map_err(ControlError::Spawn)?;
        link.attach_reader(reader);
        Ok(Self {
            peer,
            link,
            state: State::Uninitialized,
            sent: 0,
            timeout,
        })
    }
    /// Requests initialization. Capabilities outside the pinned advertised
    /// set are refused locally, before any bytes reach the peer.
    pub fn initialize(&mut self, capabilities: &[&str]) -> Result<Admission, ControlError> {
        if !matches!(self.state, State::Uninitialized) {
            return Err(ControlError::Refused(
                "the control session is already initialized or closed".into(),
            ));
        }
        for capability in capabilities {
            if !contract::admitted_capability(capability) {
                return Err(ControlError::Refused(format!(
                    "capability {capability} is not part of the pinned advertised set"
                )));
            }
        }
        let expected = self.next_correlation();
        let frame = rpc::request(Method::Initialize, &expected, Some(capabilities))
            .map_err(|error| ControlError::Frame(error.to_string()))?;
        let admission = self.round_trip(&frame, &expected, |reply| {
            let result = InitializeResult::checked(reply)?;
            let admission = Admission::checked(result).map_err(ControlError::Identity)?;
            Ok(admission)
        })?;
        if admission.generation() != self.sent {
            return Err(ControlError::Identity(format!(
                "initialize generation {} does not match the {} admitted envelopes",
                admission.generation(),
                self.sent
            )));
        }
        self.state = State::Initialized(admission.session().clone());
        Ok(admission)
    }
    /// Completes the session: shutdown reply, EOF, reap and exit check.
    pub fn shutdown(mut self) -> Result<Completed, ControlError> {
        let labels = match &self.state {
            State::Initialized(labels) => labels.clone(),
            State::Uninitialized => {
                return Err(ControlError::Refused(
                    "shutdown requires an initialized control session".into(),
                ));
            }
            State::Closed => {
                return Err(ControlError::Refused(
                    "the control session is closed".into(),
                ));
            }
        };
        let expected = self.next_correlation();
        let frame = rpc::request(Method::Shutdown, &expected, None)
            .map_err(|error| ControlError::Frame(error.to_string()))?;
        let expected_generation = self.sent;
        let shutdown = self.round_trip(&frame, &expected, |reply| {
            let result = ShutdownResult::checked(reply)?;
            if result.session() != &labels {
                return Err(ControlError::Identity(
                    "shutdown reply carries different session labels".into(),
                ));
            }
            Ok(result)
        })?;
        if shutdown.generation != expected_generation {
            return Err(ControlError::Identity(format!(
                "shutdown generation {} does not match the {} admitted envelopes",
                shutdown.generation, expected_generation
            )));
        }
        self.peer.try_kill();
        let stderr = self.peer.stderr();
        let exit_code = self.peer.reap().map_err(ControlError::Io)?;
        self.link.close_stdin();
        self.link.join_reader();
        self.state = State::Closed;
        if exit_code != 0 {
            return Err(ControlError::Io(format!(
                "peer exited with {exit_code} after a successful shutdown"
            )));
        }
        Ok(Completed {
            shutdown,
            exit_code,
            stderr,
        })
    }
    fn next_correlation(&mut self) -> String {
        self.sent = self.sent.saturating_add(1);
        format!("r{}", self.sent)
    }
    fn round_trip<T>(
        &mut self,
        frame: &[u8],
        expected: &str,
        interpret: impl Fn(&Reply) -> Result<T, ControlError>,
    ) -> Result<T, ControlError> {
        self.link
            .send(frame)
            .map_err(|reason| ControlError::Frame(reason.into()))?;
        let raw = match self.link.receive(self.timeout) {
            Ok(raw) => raw,
            Err(reason) => {
                self.peer.try_kill();
                let _ = self.peer.reap();
                self.state = State::Closed;
                let error = if reason.contains("deadline") {
                    ControlError::Deadline
                } else {
                    ControlError::Io(reason)
                };
                return Err(error);
            }
        };
        let reply = Reply::parse(&raw)?;
        if reply.correlation_text() != Some(expected) {
            return Err(ControlError::Identity(format!(
                "reply correlation {} does not match the request",
                reply.correlation_text().unwrap_or("<absent>")
            )));
        }
        match reply {
            Reply::Result { .. } => interpret(&reply),
            Reply::Failure { failure, .. } => Err(ControlError::Peer {
                code: failure.code,
                message: failure.message.into_string(),
                category: failure.category.map(|category| category.into_string()),
            }),
        }
    }
}

//! Shared-stdio transport DTOs for the pinned writfold.agent/1 contract.

pub mod message;
pub mod parse;
pub mod results;

pub use message::{Correlation, Failure, FrameError, Method, Reply, request};
pub use parse::{Bounds, ParseError, Value};
pub use results::{InitializeResult, SessionLabels, ShutdownResult};

/// Frame ceiling of the consumed contract, LF inclusive, both directions.
pub const FRAME_LIMIT: usize = 65_536;

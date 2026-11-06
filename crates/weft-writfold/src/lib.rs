#![forbid(unsafe_code)]
//! Ordinary shared-stdio client for the owner-pinned `writfold.agent/1`
//! control contract.
//!
//! Scope: transport control only. This client initializes a real `writfold
//! serve` process, binds its ephemeral session identity, enforces the pinned
//! contract digest, the 65,536-byte frame ceiling, correlated replies and a
//! monotonic generation per admitted envelope, then shuts down and reaps the
//! owned child. It requests no data service and none exists in this profile:
//! citation resolution, assessment, retention and effects remain unavailable
//! WR1-WR8 blockers, a successful handshake grants no grounding, and Weft
//! reports stay `writfold_grounded: false` and `effect_authority: false`.
//!
//! There is no fallback host, no invented method and no mock service.

mod child;
pub mod contract;
mod frame;
mod session;
#[cfg(test)]
mod tests;

pub use session::{Client, Completed, ControlError};

//! Deterministic projection of a completed `writfold.agent/1` control session.
//!
//! The envelope records exactly what a control handshake establishes —
//! transport identity — and nothing more: it re-states non-grounding and
//! non-authority on every output, in both views.

use crate::json::{Json, Result};
use crate::{View, rpc};

pub const SESSION_SCHEMA: &str = "weft.control/1";
pub const PROFILE_SCOPE: &str = "writfold.agent/1 transport-control-only";
pub const BOUNDARY: &str = "Control transport only: no corpus, assessment, retention or effect service exists \
     in this profile; this session grounds nothing and authorizes nothing";

/// What a completed session proved about the peer, nothing else.
pub struct SessionView<'a> {
    pub command: &'a str,
    pub binary_sha256: Option<&'a str>,
    pub instance: &'a str,
    pub incarnation: &'a str,
    pub server_version: &'a str,
    pub contract_sha256: &'a str,
    pub initialize_generation: u64,
    pub shutdown_generation: u64,
    pub exit_code: u64,
}
/// A refused or failed control attempt; no session identity is invented.
pub struct FailureView<'a> {
    pub command: &'a str,
    pub binary_sha256: Option<&'a str>,
    pub reason: &'a str,
}
pub fn render_session(view: &SessionView<'_>, view_kind: View, limit: usize) -> Result<Vec<u8>> {
    let mut j = Json::new(limit, matches!(view_kind, View::Human));
    if matches!(view_kind, View::Human) {
        j.raw(
            "Weft control session — transport identity only; not grounded; no effect authority.\n",
        )?;
    }
    j.object(|j| {
        j.text("schema", SESSION_SCHEMA)?;
        j.text("kind", "control-session")?;
        j.text("scope", PROFILE_SCOPE)?;
        peer(&mut *j, view.command, view.binary_sha256)?;
        j.field("session", |j| {
            j.object(|j| {
                j.text("instance_id", view.instance)?;
                j.text("incarnation", view.incarnation)?;
                j.text("server_version", view.server_version)?;
                j.text("contract_sha256", view.contract_sha256)?;
                j.count("initialize_generation", view.initialize_generation)?;
                j.count("shutdown_generation", view.shutdown_generation)?;
                Ok(())
            })
        })?;
        j.text("execution", "complete")?;
        non_authority(&mut *j)
    })?;
    j.raw("\n")?;
    Ok(j.finish())
}
pub fn render_failure(view: &FailureView<'_>, view_kind: View, limit: usize) -> Result<Vec<u8>> {
    let mut j = Json::new(limit, matches!(view_kind, View::Human));
    if matches!(view_kind, View::Human) {
        j.raw("Weft control session — refused or failed; nothing was established.\n")?;
    }
    j.object(|j| {
        j.text("schema", SESSION_SCHEMA)?;
        j.text("kind", "control-session")?;
        j.text("scope", PROFILE_SCOPE)?;
        peer(&mut *j, view.command, view.binary_sha256)?;
        j.text("execution", "failed")?;
        j.field("diagnostics", |j| {
            j.array(|j| {
                j.object(|j| {
                    j.text("code", "ControlFailure")?;
                    j.text("phase", "peer")?;
                    j.text("message", view.reason)?;
                    Ok(())
                })
            })
        })?;
        non_authority(&mut *j)
    })?;
    j.raw("\n")?;
    Ok(j.finish())
}
fn peer(j: &mut Json, command: &str, binary_sha256: Option<&str>) -> Result<()> {
    j.field("peer", |j| {
        j.object(|j| {
            j.text("command", command)?;
            match binary_sha256 {
                Some(digest) => j.text("sha256", digest)?,
                None => j.text("sha256", "unverified")?,
            }
            Ok(())
        })
    })
}
fn non_authority(j: &mut Json) -> Result<()> {
    j.flag("writfold_grounded", false)?;
    j.flag("effect_authority", false)?;
    j.text("boundary", BOUNDARY)?;
    Ok(())
}
/// The pinned frame ceiling this projection always assumes.
pub const FRAME_CEILING: usize = rpc::FRAME_LIMIT;
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn session_projection_is_complete_and_ungrounded() -> Result<(), String> {
        let view = SessionView {
            command: "writfold serve",
            binary_sha256: Some("ab"),
            instance: "i",
            incarnation: "c",
            server_version: "0.1.0-dev.0",
            contract_sha256: "b673d10f7c14c73d8f5778cfb9b2e84a98a159f1553d5c008054402ee85e7be2",
            initialize_generation: 1,
            shutdown_generation: 2,
            exit_code: 0,
        };
        let bytes = render_session(&view, View::Json, 65_536).map_err(|e| e.to_string())?;
        let text = String::from_utf8_lossy(&bytes).into_owned();
        for required in [
            "\"schema\":\"weft.control/1\"",
            "\"execution\":\"complete\"",
            "\"writfold_grounded\":false",
            "\"effect_authority\":false",
        ] {
            if !text.contains(required) {
                return Err(format!("projection lost {required}"));
            }
        }
        Ok(())
    }
}

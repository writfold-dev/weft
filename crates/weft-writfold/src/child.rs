//! Owned peer process: spawn over real pipes and never leak a child.
//!
//! The client owns the spawned process for its whole lifetime. Dropping the
//! handle kills a still-running child and reaps it; there is no path that
//! leaves an orphan behind, including error and timeout paths.

use std::{
    io::Read,
    process::{Child, Command, Stdio},
};

/// An owned `writfold serve` process (or a test peer with the same shape).
pub(crate) struct Peer {
    child: Child,
}
impl Peer {
    /// Spawns the pinned server command shape: one argument, three pipes,
    /// no shell, no inherited environment mutations.
    pub(crate) fn spawn(program: &str, argument: &str) -> Result<Self, String> {
        let child = Command::new(program)
            .arg(argument)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .map_err(|error| format!("cannot start {program} {argument}: {error}"))?;
        Ok(Self { child })
    }
    pub(crate) fn try_kill(&mut self) {
        let _ = self.child.kill();
    }
    /// Blocks until the child exits and reports its code; a preceding kill or
    /// completed shutdown must bound the wait.
    pub(crate) fn reap(&mut self) -> Result<u64, String> {
        self.child
            .wait()
            .map_err(|error| format!("cannot reap owned child: {error}"))
            .and_then(|status| {
                status
                    .code()
                    .and_then(|code| u64::try_from(code).ok())
                    .ok_or_else(|| "owned child exited without a representable code".into())
            })
    }
    /// Reads whatever the child wrote to stderr, bounded; only valid after
    /// exit, so the pipe cannot grow while reading.
    pub(crate) fn stderr(&mut self) -> Vec<u8> {
        let mut bytes = Vec::new();
        if let Some(stderr) = self.child.stderr.take() {
            let mut stderr = stderr.take(65_536);
            let _ = stderr.read_to_end(&mut bytes);
        }
        bytes
    }
    pub(crate) fn parts(
        &mut self,
    ) -> Result<(std::process::ChildStdin, std::process::ChildStdout), String> {
        let stdin = self
            .child
            .stdin
            .take()
            .ok_or_else(|| "child stdin is not piped".to_string())?;
        let stdout = self
            .child
            .stdout
            .take()
            .ok_or_else(|| "child stdout is not piped".to_string())?;
        Ok((stdin, stdout))
    }
}
impl Drop for Peer {
    fn drop(&mut self) {
        self.try_kill();
        let _ = self.child.wait();
    }
}

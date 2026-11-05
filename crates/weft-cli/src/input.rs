use sha2::{Digest, Sha256};
use std::{fs::File, io::Read, path::Path};
use weft_domain::{Code, Diagnostic, Phase};

pub(crate) struct Loaded {
    pub bytes: Vec<u8>,
    pub sha256: String,
}
pub(crate) fn load(path: &Path, limit: usize) -> Result<Loaded, Diagnostic> {
    let initial = std::fs::metadata(path)
        .map_err(|error| unavailable(format!("Cannot inspect source: {error}")))?;
    if !initial.is_file() {
        return Err(unavailable(
            "Source must be a regular file; streams and devices are not accepted",
        ));
    }
    let mut file =
        File::open(path).map_err(|error| unavailable(format!("Cannot open source: {error}")))?;
    let metadata = file
        .metadata()
        .map_err(|error| unavailable(format!("Cannot inspect source: {error}")))?;
    if !metadata.is_file() {
        return Err(unavailable(
            "Source must be a regular file; streams and devices are not accepted",
        ));
    }
    let bound =
        u64::try_from(limit).map_err(|_| unavailable("Source byte limit is not representable"))?;
    if metadata.len() > bound {
        return Err(limit_error(limit));
    }
    let mut bytes = Vec::new();
    let mut chunk = [0_u8; 8192];
    loop {
        let count = file
            .read(&mut chunk)
            .map_err(|error| unavailable(format!("Cannot read complete source: {error}")))?;
        if count == 0 {
            break;
        }
        let remaining = limit
            .checked_sub(bytes.len())
            .ok_or_else(|| limit_error(limit))?;
        if count > remaining {
            return Err(limit_error(limit));
        }
        bytes.extend_from_slice(&chunk[..count]);
    }
    let digest = Sha256::digest(&bytes);
    use std::fmt::Write;
    let mut sha256 = String::with_capacity(64);
    for byte in digest {
        write!(&mut sha256, "{byte:02x}")
            .map_err(|_| unavailable("Cannot format source digest"))?;
    }
    Ok(Loaded { bytes, sha256 })
}
fn unavailable(message: impl Into<String>) -> Diagnostic {
    Diagnostic::new(Code::InputUnavailable, Phase::Input, message, None)
}
fn limit_error(limit: usize) -> Diagnostic {
    let mut diagnostic = Diagnostic::new(
        Code::LimitExceeded,
        Phase::Input,
        "Source exceeds the admitted byte bound; no partial source is analyzed or hashed",
        None,
    );
    diagnostic.expected = Some(format!("at most {limit} bytes").into_boxed_str());
    diagnostic.help = Some("Reduce the source size before analysis".into());
    diagnostic
}

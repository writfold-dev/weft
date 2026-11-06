//! Checked conversions for writfold.agent/1 control results.
//!
//! Every field of the pinned response schema is validated; unknown or missing
//! fields, wrong literals and out-of-range counters are refusals, never
//! defaults. These conversions check shape and schema constants only; binding
//! the session to the exact pinned artifact identity belongs to the client.

use super::message::{Correlation, FrameError, Reply, unsigned_lexical};
use super::parse::Value;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SessionLabels {
    pub instance: Box<str>,
    pub incarnation: Box<str>,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InitializeResult {
    pub profile: Box<str>,
    pub implementation_scope: Box<str>,
    pub server_name: Box<str>,
    pub server_version: Box<str>,
    pub session: SessionLabels,
    pub generation: u64,
    pub capabilities: Vec<Box<str>>,
    pub batch: bool,
    pub notifications: bool,
    pub max_request_bytes: u64,
    pub max_response_bytes: u64,
    pub methods: Vec<Box<str>>,
    pub contract_namespace: Box<str>,
    pub contract_schema: u64,
    pub contract_sha256: Box<str>,
    pub trust_boundary: Box<str>,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ShutdownResult {
    pub exit_code: u64,
    pub complete: bool,
    pub generation: u64,
    pub session: SessionLabels,
}
impl InitializeResult {
    pub fn checked(reply: &Reply) -> std::result::Result<Self, FrameError> {
        let result = reply_body(reply, "initialize")?;
        let fields = Fields::new(result, "initialize result");
        let server = fields.object("server")?;
        let session = fields.object("session")?;
        let methods = fields.object("methods")?;
        let contract = fields.object("contract")?;
        fields.const_text(
            "protocol_version",
            super::message::PROTOCOL_VERSION,
            "protocol version",
        )?;
        let checked = Self {
            profile: fields.const_text("profile", "writfold.agent/1", "profile")?,
            implementation_scope: fields.const_text(
                "implementation_scope",
                "transport-control-only",
                "implementation scope",
            )?,
            server_name: const_in(server, "name", "writfold", "server name")?,
            server_version: text_in(server, "version", "server version")?,
            session: labels(session)?,
            generation: fields.unsigned("generation", "initialize generation")?,
            capabilities: fields.string_array("capabilities", "capabilities")?,
            batch: fields.const_flag("batch", false, "batch")?,
            notifications: fields.const_flag("notifications", true, "notifications")?,
            max_request_bytes: fields.unsigned("max_request_bytes", "max_request_bytes")?,
            max_response_bytes: fields.unsigned("max_response_bytes", "max_response_bytes")?,
            methods: keys(methods, "methods")?,
            contract_namespace: const_in(
                contract,
                "namespace",
                "writfold-agent-contract",
                "contract namespace",
            )?,
            contract_schema: unsigned_in(contract, "schema", "contract schema")?,
            contract_sha256: hex64_in(contract, "sha256", "contract digest")?,
            trust_boundary: fields.const_text(
                "trust_boundary",
                "Transport/session control only; no authorized corpus, retained release, \
                 grounding or effect service is available.",
                "trust boundary",
            )?,
        };
        fields.exact(&[
            "protocol_version",
            "profile",
            "implementation_scope",
            "server",
            "session",
            "generation",
            "capabilities",
            "batch",
            "notifications",
            "max_request_bytes",
            "max_response_bytes",
            "methods",
            "contract",
            "trust_boundary",
        ])?;
        exact_keys(server, &["name", "version"], "server")?;
        exact_keys(session, &["instance_id", "incarnation"], "session")?;
        exact_keys(methods, &["initialize", "shutdown"], "methods")?;
        exact_keys(contract, &["namespace", "schema", "sha256"], "contract")?;
        Ok(checked)
    }
}
impl ShutdownResult {
    pub fn checked(reply: &Reply) -> std::result::Result<Self, FrameError> {
        let result = reply_body(reply, "shutdown")?;
        let fields = Fields::new(result, "shutdown result");
        let session = fields.object("session")?;
        let payload = fields.object("payload")?;
        let checked = Self {
            exit_code: fields.const_unsigned("exit_code", 0, "shutdown exit code")?,
            complete: fields.const_flag("complete", true, "shutdown completeness")?,
            generation: fields.unsigned("generation", "shutdown generation")?,
            session: labels(session)?,
        };
        fields.exact(&["exit_code", "complete", "generation", "session", "payload"])?;
        exact_keys(session, &["instance_id", "incarnation"], "session")?;
        exact_keys(payload, &["shutdown"], "payload")?;
        match payload.iter().find(|(known, _)| &**known == "shutdown") {
            Some((_, Value::Bool(true))) => Ok(()),
            _ => Err(FrameError::Shape("payload shutdown")),
        }?;
        Ok(checked)
    }
    pub fn session(&self) -> &SessionLabels {
        &self.session
    }
}
fn reply_body<'r>(
    reply: &'r Reply,
    part: &'static str,
) -> std::result::Result<&'r [(Box<str>, Value)], FrameError> {
    match reply {
        Reply::Result {
            result: Value::Object(members),
            ..
        } => Ok(members),
        _ => Err(FrameError::Shape(part)),
    }
}
fn labels(session: &[(Box<str>, Value)]) -> std::result::Result<SessionLabels, FrameError> {
    Ok(SessionLabels {
        instance: label(session, "instance_id")?,
        incarnation: label(session, "incarnation")?,
    })
}
fn label(session: &[(Box<str>, Value)], key: &str) -> std::result::Result<Box<str>, FrameError> {
    let value = session
        .iter()
        .find(|(known, _)| &**known == key)
        .map(|(_, value)| value)
        .ok_or(FrameError::Shape("session label is absent"))?;
    let text = match value {
        Value::Text(text) => text,
        _ => return Err(FrameError::Shape("session label is not a string")),
    };
    let label = text
        .chars()
        .next()
        .is_some_and(|first| first.is_ascii_alphanumeric())
        .then(|| {
            text.chars()
                .skip(1)
                .all(|rest| rest.is_ascii_alphanumeric() || matches!(rest, '_' | '.' | ':' | '-'))
        })
        .ok_or(FrameError::Shape(
            "session label is not an admitted spelling",
        ))?;
    if label {
        Ok(text.clone())
    } else {
        Err(FrameError::Shape(
            "session label is not an admitted spelling",
        ))
    }
}
fn keys(
    object: &[(Box<str>, Value)],
    part: &'static str,
) -> std::result::Result<Vec<Box<str>>, FrameError> {
    object
        .iter()
        .map(|(key, value)| match value {
            Value::Object(_) => Ok(key.clone()),
            _ => Err(FrameError::Shape(part)),
        })
        .collect()
}
struct Fields<'v> {
    members: &'v [(Box<str>, Value)],
    part: &'static str,
}
impl<'v> Fields<'v> {
    fn new(members: &'v [(Box<str>, Value)], part: &'static str) -> Self {
        Self { members, part }
    }
    fn find(&self, key: &str) -> Option<&'v Value> {
        self.members
            .iter()
            .find(|(known, _)| &**known == key)
            .map(|(_, value)| value)
    }
    fn object(&self, key: &str) -> std::result::Result<&'v [(Box<str>, Value)], FrameError> {
        match self.find(key) {
            Some(Value::Object(members)) => Ok(members),
            _ => Err(FrameError::Shape(self.part)),
        }
    }
    fn unsigned(&self, key: &str, part: &'static str) -> std::result::Result<u64, FrameError> {
        match self.find(key) {
            Some(Value::Number(token)) => unsigned_lexical(token).ok_or(FrameError::Shape(part)),
            _ => Err(FrameError::Shape(part)),
        }
    }
    fn const_unsigned(
        &self,
        key: &str,
        expected: u64,
        part: &'static str,
    ) -> std::result::Result<u64, FrameError> {
        let observed = self.unsigned(key, part)?;
        (observed == expected)
            .then_some(expected)
            .ok_or(FrameError::Shape(part))
    }
    fn const_flag(
        &self,
        key: &str,
        expected: bool,
        part: &'static str,
    ) -> std::result::Result<bool, FrameError> {
        match self.find(key) {
            Some(Value::Bool(observed)) if *observed == expected => Ok(expected),
            _ => Err(FrameError::Shape(part)),
        }
    }
    fn const_text(
        &self,
        key: &str,
        expected: &str,
        part: &'static str,
    ) -> std::result::Result<Box<str>, FrameError> {
        const_in(self.members, key, expected, part)
    }
    fn string_array(
        &self,
        key: &str,
        part: &'static str,
    ) -> std::result::Result<Vec<Box<str>>, FrameError> {
        match self.find(key) {
            Some(Value::Array(items)) => items
                .iter()
                .map(|item| match item {
                    Value::Text(text) => Ok(text.clone()),
                    _ => Err(FrameError::Shape(part)),
                })
                .collect(),
            _ => Err(FrameError::Shape(part)),
        }
    }
    fn exact(&self, expected: &[&str]) -> std::result::Result<(), FrameError> {
        exact_keys(self.members, expected, self.part)
    }
}
fn const_in(
    members: &[(Box<str>, Value)],
    key: &str,
    expected: &str,
    part: &'static str,
) -> std::result::Result<Box<str>, FrameError> {
    match members
        .iter()
        .find(|(known, _)| &**known == key)
        .map(|(_, value)| value)
    {
        Some(Value::Text(text)) if &**text == expected => Ok(text.clone()),
        _ => Err(FrameError::Shape(part)),
    }
}
fn text_in(
    members: &[(Box<str>, Value)],
    key: &str,
    part: &'static str,
) -> std::result::Result<Box<str>, FrameError> {
    match members
        .iter()
        .find(|(known, _)| &**known == key)
        .map(|(_, value)| value)
    {
        Some(Value::Text(text)) => Ok(text.clone()),
        _ => Err(FrameError::Shape(part)),
    }
}
fn unsigned_in(
    members: &[(Box<str>, Value)],
    key: &str,
    part: &'static str,
) -> std::result::Result<u64, FrameError> {
    match members
        .iter()
        .find(|(known, _)| &**known == key)
        .map(|(_, value)| value)
    {
        Some(Value::Number(token)) => unsigned_lexical(token).ok_or(FrameError::Shape(part)),
        _ => Err(FrameError::Shape(part)),
    }
}
fn hex64_in(
    members: &[(Box<str>, Value)],
    key: &str,
    part: &'static str,
) -> std::result::Result<Box<str>, FrameError> {
    let text = text_in(members, key, part)?;
    (text.len() == 64
        && text
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte)))
    .then_some(text)
    .ok_or(FrameError::Shape(part))
}
fn exact_keys(
    members: &[(Box<str>, Value)],
    expected: &[&str],
    part: &'static str,
) -> std::result::Result<(), FrameError> {
    if members.len() != expected.len() || members.iter().any(|(key, _)| !expected.contains(&&**key))
    {
        return Err(FrameError::Shape(part));
    }
    Ok(())
}
/// Exposed for tests: correlation stays opaque to conversions.
pub fn notification_correlation() -> Correlation {
    Correlation::Notification
}

//! Typed JSON-RPC 2.0 frames for the consumed writfold.agent/1 contract.
//!
//! Requests are rendered from typed methods only; replies are parsed strictly
//! and converted through checked constructors. Unadmitted spellings, unknown
//! fields, duplicate keys and non-integral correlation numbers are refused
//! instead of repaired.

use super::parse::{Bounds, ParseError, Value, parse};
use crate::json::{Json, RenderError, Result};

pub const PROTOCOL_VERSION: &str = "2";
const MAX_U64: u128 = u64::MAX as u128;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Correlation {
    Notification,
    Text(Box<str>),
    Number(Box<str>),
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Failure {
    pub code: i64,
    pub message: Box<str>,
    pub category: Option<Box<str>>,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Reply {
    Result {
        correlation: Correlation,
        result: Value,
    },
    Failure {
        correlation: Correlation,
        failure: Failure,
    },
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FrameError {
    Parse(ParseError),
    Shape(&'static str),
    NotImplemented,
}
impl From<ParseError> for FrameError {
    fn from(error: ParseError) -> Self {
        Self::Parse(error)
    }
}
impl std::fmt::Display for FrameError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Parse(error) => write!(formatter, "malformed JSON frame: {error:?}"),
            Self::Shape(part) => write!(formatter, "reply deviates from the pinned shape: {part}"),
            Self::NotImplemented => write!(formatter, "frame method is not implemented here"),
        }
    }
}
impl std::error::Error for FrameError {}

/// The two methods this client is allowed to invoke; unavailable peer services
/// are not representable, so they can never be requested by accident.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Method {
    Initialize,
    Shutdown,
}
impl Method {
    pub fn name(self) -> &'static str {
        match self {
            Self::Initialize => "initialize",
            Self::Shutdown => "shutdown",
        }
    }
}
/// Renders one newline-delimited request frame, LF included.
pub fn request(
    method: Method,
    correlation: &str,
    capabilities: Option<&[&str]>,
) -> Result<Vec<u8>> {
    let mut j = Json::new(super::FRAME_LIMIT, false);
    j.object(|j| {
        j.text("jsonrpc", "2.0")?;
        j.text("id", correlation)?;
        j.text("method", method.name())?;
        match (method, capabilities) {
            (Method::Initialize, Some(admitted)) => j.field("params", |j| {
                j.object(|j| {
                    j.text("protocol_version", PROTOCOL_VERSION)?;
                    j.field("capabilities", |j| {
                        j.array(|j| {
                            for capability in admitted {
                                j.item(|j| j.string(capability))?;
                            }
                            Ok(())
                        })
                    })
                })
            }),
            _ => Ok(()),
        }
    })?;
    j.raw("\n")?;
    let mut frame = j.finish();
    if frame.len() > super::FRAME_LIMIT {
        return Err(RenderError::OutputLimit);
    }
    frame.shrink_to_fit();
    Ok(frame)
}
impl Reply {
    /// Parses a complete reply frame (without the delimiting LF).
    pub fn parse(frame: &[u8]) -> std::result::Result<Self, FrameError> {
        let value = parse(frame, Bounds::transport())?;
        let Value::Object(members) = &value else {
            return Err(FrameError::Shape("reply is not an object"));
        };
        let mut reply_key = None;
        let mut body: Option<&Value> = None;
        let mut failure = false;
        for (key, member) in members {
            match &**key {
                "jsonrpc" => {
                    text(member, "2.0", "jsonrpc version")?;
                }
                "id" => reply_key = Some(correlation(member)?),
                "result" if body.is_none() => body = Some(member),
                "error" if body.is_none() => {
                    failure = true;
                    body = Some(member);
                }
                _ => return Err(FrameError::Shape("unknown reply field")),
            }
        }
        let reply_key = reply_key.ok_or(FrameError::Shape("reply correlation is absent"))?;
        let body = body.ok_or(FrameError::Shape("reply carries neither result nor error"))?;
        if failure {
            return Ok(Self::Failure {
                correlation: reply_key,
                failure: failure_body(body)?,
            });
        }
        Ok(Self::Result {
            correlation: reply_key,
            result: body.clone(),
        })
    }
    pub fn correlation_text(&self) -> Option<&str> {
        match self {
            Self::Result {
                correlation: Correlation::Text(text),
                ..
            }
            | Self::Failure {
                correlation: Correlation::Text(text),
                ..
            } => Some(text),
            _ => None,
        }
    }
}
fn text(value: &Value, expected: &str, part: &'static str) -> std::result::Result<(), FrameError> {
    match value {
        Value::Text(actual) if &**actual == expected => Ok(()),
        _ => Err(FrameError::Shape(part)),
    }
}
fn u64_value(value: &Value, part: &'static str) -> std::result::Result<u64, FrameError> {
    let Value::Number(token) = value else {
        return Err(FrameError::Shape(part));
    };
    unsigned_lexical(token).ok_or(FrameError::Shape(part))
}
pub fn unsigned_lexical(token: &str) -> Option<u64> {
    if token.is_empty() || !token.bytes().all(|byte| byte.is_ascii_digit()) {
        return None;
    }
    let parsed: u128 = token.parse().ok()?;
    (parsed <= MAX_U64).then_some(parsed as u64)
}
/// Integer correlation tokens only: fraction/exponent spellings are refused
/// even when mathematically integral, per the pinned contract.
fn integral_lexical(token: &str) -> bool {
    let digits = token.strip_prefix('-').unwrap_or(token);
    !digits.is_empty() && digits.bytes().all(|byte| byte.is_ascii_digit())
}
fn correlation(value: &Value) -> std::result::Result<Correlation, FrameError> {
    match value {
        Value::Null => Ok(Correlation::Notification),
        Value::Text(text) => Ok(Correlation::Text(text.clone())),
        Value::Number(token) if integral_lexical(token) => Ok(Correlation::Number(token.clone())),
        _ => Err(FrameError::Shape(
            "correlation is neither string, integer nor null",
        )),
    }
}
fn failure_body(value: &Value) -> std::result::Result<Failure, FrameError> {
    let Value::Object(members) = value else {
        return Err(FrameError::Shape("error body is not an object"));
    };
    let mut code = None;
    let mut message = None;
    let mut category = None;
    for (key, member) in members {
        match &**key {
            "code" => code = Some(number_i64(member)?),
            "message" => message = Some(text_clone(member)?),
            "data" => category = data_category(member)?,
            _ => return Err(FrameError::Shape("unknown error field")),
        }
    }
    Ok(Failure {
        code: code.ok_or(FrameError::Shape("error code is absent"))?,
        message: message.ok_or(FrameError::Shape("error message is absent"))?,
        category,
    })
}
fn data_category(value: &Value) -> std::result::Result<Option<Box<str>>, FrameError> {
    let Value::Object(members) = value else {
        return Err(FrameError::Shape("error data is not an object"));
    };
    let mut category = None;
    for (key, member) in members {
        match &**key {
            "schema_version" => {
                u64_value(member, "error data schema version")?;
            }
            "category" => category = Some(text_clone(member)?),
            "message" => {}
            "diagnostic" => {
                let Value::Object(inner) = member else {
                    return Err(FrameError::Shape("error diagnostic is not an object"));
                };
                for (inner_key, _) in inner {
                    if !matches!(&**inner_key, "code" | "detail" | "field" | "span") {
                        return Err(FrameError::Shape("unknown diagnostic field"));
                    }
                }
            }
            _ => return Err(FrameError::Shape("unknown error data field")),
        }
    }
    Ok(category)
}
fn number_i64(value: &Value) -> std::result::Result<i64, FrameError> {
    let Value::Number(token) = value else {
        return Err(FrameError::Shape("error code is not numeric"));
    };
    if token
        .bytes()
        .any(|byte| !matches!(byte, b'-' | b'0'..=b'9'))
    {
        return Err(FrameError::Shape("error code is not an integer token"));
    }
    token
        .parse::<i64>()
        .map_err(|_| FrameError::Shape("error code is out of range"))
}
fn text_clone(value: &Value) -> std::result::Result<Box<str>, FrameError> {
    match value {
        Value::Text(text) => Ok(text.clone()),
        _ => Err(FrameError::Shape("expected a string")),
    }
}

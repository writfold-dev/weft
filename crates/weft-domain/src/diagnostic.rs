use crate::SourceSpan;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Phase {
    Input,
    Lex,
    Parse,
    Resolve,
    Type,
    Capture,
    Lower,
    Evaluate,
    Report,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Code {
    InputUnavailable,
    InvalidUtf8,
    InvalidCharacter,
    InvalidEscape,
    InvalidNatural,
    UnterminatedString,
    UnexpectedToken,
    DuplicateName,
    UnknownName,
    WrongNameKind,
    DuplicateRule,
    TypeMismatch,
    ArityMismatch,
    AmbiguousType,
    UnsupportedProfile,
    UnresolvedInput,
    UnqualifiedRule,
    InvalidPremise,
    LimitExceeded,
    InvalidProgram,
    OutputUnavailable,
    InvalidArguments,
}
impl Code {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::InputUnavailable => "WF1001",
            Self::InvalidUtf8 => "WF1002",
            Self::InvalidCharacter => "WF1101",
            Self::InvalidEscape => "WF1102",
            Self::InvalidNatural => "WF1103",
            Self::UnterminatedString => "WF1104",
            Self::UnexpectedToken => "WF1201",
            Self::DuplicateName => "WF1301",
            Self::UnknownName => "WF1302",
            Self::WrongNameKind => "WF1303",
            Self::DuplicateRule => "WF1304",
            Self::TypeMismatch => "WF1401",
            Self::ArityMismatch => "WF1402",
            Self::AmbiguousType => "WF1403",
            Self::UnsupportedProfile => "WF1501",
            Self::UnresolvedInput => "WF1502",
            Self::UnqualifiedRule => "WF1503",
            Self::InvalidPremise => "WF1504",
            Self::LimitExceeded => "WF1601",
            Self::InvalidProgram => "WF1602",
            Self::OutputUnavailable => "WF1701",
            Self::InvalidArguments => "WF1003",
        }
    }
}
#[derive(Clone, Debug)]
pub struct Label {
    pub span: SourceSpan,
    pub message: String,
}
#[derive(Clone, Debug)]
pub struct Diagnostic {
    pub code: Code,
    pub phase: Phase,
    pub message: Box<str>,
    pub primary: Option<SourceSpan>,
    pub secondary: Vec<Label>,
    pub expected: Option<Box<str>>,
    pub actual: Option<Box<str>>,
    pub help: Option<Box<str>>,
}
impl Diagnostic {
    pub fn new(
        code: Code,
        phase: Phase,
        message: impl Into<String>,
        primary: Option<SourceSpan>,
    ) -> Self {
        Self {
            code,
            phase,
            message: message.into().into_boxed_str(),
            primary,
            secondary: Vec::new(),
            expected: None,
            actual: None,
            help: None,
        }
    }
}

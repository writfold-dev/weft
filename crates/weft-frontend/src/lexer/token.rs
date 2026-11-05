use std::borrow::Cow;
use weft_domain::SourceSpan;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Kind {
    Ident,
    String,
    Natural,
    Keyword(&'static str),
    LeftBrace,
    RightBrace,
    LeftParen,
    RightParen,
    Semicolon,
    Comma,
    Dot,
    Spread,
    Colon,
    Bind,
    Assign,
    Equal,
    NotEqual,
    SubsetOrEqual,
    Pipe,
    Ampersand,
    Minus,
    End,
}

impl Kind {
    pub(super) fn word(word: &str) -> Self {
        match word {
            "review" => Self::Keyword("review"),
            "context" => Self::Keyword("context"),
            "at" => Self::Keyword("at"),
            "profile" => Self::Keyword("profile"),
            "target" => Self::Keyword("target"),
            "proposal" => Self::Keyword("proposal"),
            "claim" => Self::Keyword("claim"),
            "asset" => Self::Keyword("asset"),
            "rule" => Self::Keyword("rule"),
            "citation" => Self::Keyword("citation"),
            "need" => Self::Keyword("need"),
            "assume" => Self::Keyword("assume"),
            "check" => Self::Keyword("check"),
            "by" => Self::Keyword("by"),
            "and" => Self::Keyword("and"),
            "or" => Self::Keyword("or"),
            "not" => Self::Keyword("not"),
            "true" => Self::Keyword("true"),
            "false" => Self::Keyword("false"),
            "forall" => Self::Keyword("forall"),
            "exists" => Self::Keyword("exists"),
            "in" => Self::Keyword("in"),
            _ => Self::Ident,
        }
    }

    pub(crate) fn description(self) -> &'static str {
        match self {
            Self::Ident => "identifier",
            Self::String => "quoted string",
            Self::Natural => "natural number",
            Self::Keyword(word) => word,
            Self::LeftBrace => "{",
            Self::RightBrace => "}",
            Self::LeftParen => "(",
            Self::RightParen => ")",
            Self::Semicolon => ";",
            Self::Comma => ",",
            Self::Dot => ".",
            Self::Spread => "...",
            Self::Colon => ":",
            Self::Bind => ":=",
            Self::Assign => "=",
            Self::Equal => "==",
            Self::NotEqual => "!=",
            Self::SubsetOrEqual => "<=",
            Self::Pipe => "|",
            Self::Ampersand => "&",
            Self::Minus => "-",
            Self::End => "end of source",
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) struct Token<'s> {
    pub kind: Kind,
    pub lexeme: &'s str,
    pub span: SourceSpan,
    pub text: Option<Cow<'s, str>>,
}

use super::{Kind, LexResult, Scanner, Token};
use std::borrow::Cow;
use weft_domain::Code;

impl<'s> Scanner<'s, '_> {
    pub(super) fn natural(&mut self) -> LexResult<()> {
        let start = self.position;
        while self.current().is_some_and(|ch| ch.is_ascii_digit()) {
            if self.position - start >= self.limits.natural_digits {
                return Err(self.error(
                    Code::LimitExceeded,
                    start,
                    self.position + 1,
                    "Natural literal digit limit exceeded",
                    format!("at most {} decimal digits", self.limits.natural_digits),
                    "Shorten the literal or request a larger natural-digit budget.",
                ));
            }
            self.position += 1;
        }
        let digits = self.slice(start, self.position)?;
        if digits.len() > 1 && digits.starts_with('0') {
            return Err(self.error(
                Code::InvalidNatural,
                start,
                self.position,
                "Natural literals cannot have leading zeroes",
                "0 or a nonzero decimal integer",
                "Remove leading zeroes; signs, fractions and exponents are not supported.",
            ));
        }
        if let Some(ch) = self.current()
            && (ch.is_alphanumeric() || ch == '_')
        {
            return Err(self.error(Code::InvalidNatural, start, self.position + ch.len_utf8(),
                "Natural literal is joined to a name or exponent", "a token boundary after decimal digits",
                "Separate tokens; exponent notation and digit-prefixed identifiers are not supported."));
        }
        Ok(())
    }

    pub(super) fn string(&mut self) -> LexResult<Token<'s>> {
        let start = self.position;
        self.position += 1;
        let mut chunk = self.position;
        let mut decoded: Option<String> = None;
        loop {
            match self.current() {
                Some('"') => {
                    let rest = self.slice(chunk, self.position)?;
                    let value = match decoded {
                        Some(mut value) => {
                            value.push_str(rest);
                            Cow::Owned(value)
                        }
                        None => Cow::Borrowed(rest),
                    };
                    self.position += 1;
                    return Ok(Token {
                        kind: Kind::String,
                        lexeme: self.slice(start, self.position)?,
                        span: self.span(start, self.position)?,
                        text: Some(value),
                    });
                }
                Some('\\') => {
                    let prefix = self.slice(chunk, self.position)?;
                    let value = decoded.get_or_insert_with(String::new);
                    value.push_str(prefix);
                    value.push(self.escape()?);
                    chunk = self.position;
                }
                Some(ch) if ch.is_control() => {
                    return Err(self.error(
                        Code::InvalidCharacter,
                        self.position,
                        self.position + ch.len_utf8(),
                        "Unescaped control character in string",
                        "non-control UTF-8 text or a supported escape",
                        "Use \\n, \\r or \\t for supported controls; raw newlines are forbidden.",
                    ));
                }
                Some(ch) => self.position += ch.len_utf8(),
                None => {
                    return Err(self.error(
                        Code::UnterminatedString,
                        start,
                        self.position,
                        "Unterminated quoted string",
                        "closing double quote",
                        "Close the string before the end of source.",
                    ));
                }
            }
        }
    }

    fn escape(&mut self) -> LexResult<char> {
        let start = self.position;
        self.position += 1;
        let decoded = match self.current() {
            Some('"') => '"',
            Some('\\') => '\\',
            Some('n') => '\n',
            Some('r') => '\r',
            Some('t') => '\t',
            Some(ch) => {
                return Err(self.error(
                    Code::InvalidEscape,
                    start,
                    self.position + ch.len_utf8(),
                    "Unsupported string escape",
                    "\\\", \\\\, \\n, \\r or \\t",
                    "Use a supported escape or write non-control UTF-8 text directly.",
                ));
            }
            None => {
                return Err(self.error(
                    Code::UnterminatedString,
                    start,
                    self.position,
                    "String ends after an escape introducer",
                    "escape character and closing quote",
                    "Complete the supported escape and close the string.",
                ));
            }
        };
        self.position += 1;
        Ok(decoded)
    }
}

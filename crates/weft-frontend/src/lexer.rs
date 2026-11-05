mod literals;
#[cfg(test)]
mod tests;
mod token;

pub(crate) use token::{Kind, Token};
use weft_domain::{Code, Diagnostic, Limits, Phase, SourceSpan};

type LexResult<T> = Result<T, Box<Diagnostic>>;

pub(crate) fn lex<'s>(source: &'s str, limits: &Limits) -> LexResult<Vec<Token<'s>>> {
    if source.len() > limits.source_bytes {
        let mut error = Diagnostic::new(
            Code::LimitExceeded,
            Phase::Lex,
            "Source byte limit exceeded before tokenization",
            None,
        );
        error.expected = Some(format!("at most {} bytes", limits.source_bytes).into_boxed_str());
        error.actual = Some(format!("{} bytes", source.len()).into_boxed_str());
        error.help = Some("Reduce the source size or request a larger source-byte budget.".into());
        return Err(Box::new(error));
    }
    let mut scanner = Scanner {
        source,
        limits,
        position: 0,
    };
    let mut tokens = Vec::new();
    while scanner.skip_trivia()? {
        if tokens.len() >= limits.tokens {
            let mut error = scanner.error(
                Code::LimitExceeded,
                scanner.position,
                scanner.position,
                "Token limit exceeded",
                format!("at most {} tokens", limits.tokens),
                "Reduce the source or request a larger token budget.",
            );
            error.actual = Some(
                format!(
                    "{} tokens already admitted; another token is required",
                    tokens.len()
                )
                .into_boxed_str(),
            );
            return Err(error);
        }
        tokens.push(scanner.token()?);
    }
    Ok(tokens)
}

struct Scanner<'s, 'l> {
    source: &'s str,
    limits: &'l Limits,
    position: usize,
}

impl<'s> Scanner<'s, '_> {
    fn current(&self) -> Option<char> {
        self.source
            .get(self.position..)
            .and_then(|rest| rest.chars().next())
    }

    fn starts(&self, text: &str) -> bool {
        self.source
            .get(self.position..)
            .is_some_and(|rest| rest.starts_with(text))
    }

    fn span(&self, start: usize, end: usize) -> LexResult<SourceSpan> {
        SourceSpan::checked(self.source, start, end).map_err(|_| {
            Box::new(Diagnostic::new(
                Code::InvalidProgram,
                Phase::Lex,
                "Lexer produced an invalid UTF-8 byte boundary",
                None,
            ))
        })
    }

    fn slice(&self, start: usize, end: usize) -> LexResult<&'s str> {
        self.source.get(start..end).ok_or_else(|| {
            Box::new(Diagnostic::new(
                Code::InvalidProgram,
                Phase::Lex,
                "Lexer could not borrow a source token",
                None,
            ))
        })
    }

    fn error(
        &self,
        code: Code,
        start: usize,
        end: usize,
        message: &str,
        expected: impl Into<String>,
        help: &str,
    ) -> Box<Diagnostic> {
        let span = match self.span(start, end) {
            Ok(span) => span,
            Err(error) => return error,
        };
        let actual = match self.slice(start, end) {
            Ok(text) => format!("{text:?}"),
            Err(error) => return error,
        };
        let mut error = Diagnostic::new(code, Phase::Lex, message, Some(span));
        error.expected = Some(expected.into().into_boxed_str());
        error.actual = Some(actual.into_boxed_str());
        error.help = Some(help.into());
        Box::new(error)
    }

    fn skip_trivia(&mut self) -> LexResult<bool> {
        loop {
            match self.current() {
                None => return Ok(false),
                Some(' ' | '\t' | '\n') => self.position += 1,
                Some('\r') => self.crlf()?,
                Some('/') if self.starts("//") => {
                    self.position += 2;
                    while let Some(ch) = self.current() {
                        if ch == '\n' {
                            break;
                        }
                        if ch == '\r' {
                            self.crlf()?;
                            break;
                        }
                        self.position += ch.len_utf8();
                    }
                }
                Some(_) => return Ok(true),
            }
        }
    }

    fn crlf(&mut self) -> LexResult<()> {
        if self.starts("\r\n") {
            self.position += 2;
            Ok(())
        } else {
            Err(self.error(
                Code::InvalidCharacter,
                self.position,
                self.position + 1,
                "Isolated carriage return",
                "LF or CRLF line ending",
                "Replace the isolated carriage return with LF or CRLF, including in comments.",
            ))
        }
    }

    fn token(&mut self) -> LexResult<Token<'s>> {
        let start = self.position;
        let ch = self.current().ok_or_else(|| {
            self.error(
                Code::InvalidProgram,
                start,
                start,
                "Missing source token",
                "token",
                "Report this internal lexer error.",
            )
        })?;
        if ch == '"' {
            return self.string();
        }
        let kind = if ch.is_ascii_alphabetic() || ch == '_' {
            while self
                .current()
                .is_some_and(|c| c.is_ascii_alphanumeric() || c == '_')
            {
                self.position += 1;
            }
            Kind::word(self.slice(start, self.position)?)
        } else if ch.is_ascii_digit() {
            self.natural()?;
            Kind::Natural
        } else {
            self.punctuation(ch)?
        };
        Ok(Token {
            kind,
            lexeme: self.slice(start, self.position)?,
            span: self.span(start, self.position)?,
            text: None,
        })
    }

    fn punctuation(&mut self, ch: char) -> LexResult<Kind> {
        let (kind, bytes) = match ch {
            '.' if self.starts("...") => (Kind::Spread, 3),
            ':' if self.starts(":=") => (Kind::Bind, 2),
            '=' if self.starts("==") => (Kind::Equal, 2),
            '!' if self.starts("!=") => (Kind::NotEqual, 2),
            '{' => (Kind::LeftBrace, 1), '}' => (Kind::RightBrace, 1),
            '(' => (Kind::LeftParen, 1), ')' => (Kind::RightParen, 1),
            ';' => (Kind::Semicolon, 1), ',' => (Kind::Comma, 1),
            '.' => (Kind::Dot, 1), ':' => (Kind::Colon, 1), '=' => (Kind::Assign, 1),
            _ => return Err(self.error(Code::InvalidCharacter, self.position,
                self.position + ch.len_utf8(), "Character is not a Weft token",
                "ASCII identifier, literal, delimiter, ==, !=, := or ...",
                "Remove unsupported syntax; operators must be contiguous and identifiers must be ASCII.")),
        };
        self.position += bytes;
        Ok(kind)
    }
}

use super::ParseResult;
use crate::{
    ast::{Name, Text},
    lexer::{Kind, Token},
};

use weft_domain::{Code, Diagnostic, Limits, Phase, SourceSpan, limits::MAX_SOURCE_DEPTH};

pub(super) struct Cursor<'s, 'l> {
    pub source: &'s str,
    pub limits: &'l Limits,
    tokens: Vec<Token<'s>>,
    next: usize,
    eof: SourceSpan,
    pub last: SourceSpan,
    nodes: usize,
    nesting: usize,
}

impl<'s, 'l> Cursor<'s, 'l> {
    pub fn new(source: &'s str, limits: &'l Limits, tokens: Vec<Token<'s>>) -> ParseResult<Self> {
        let eof = SourceSpan::checked(source, source.len(), source.len())
            .map_err(|_| Self::invariant("Invalid end-of-source span"))?;
        Ok(Self {
            source,
            limits,
            tokens,
            next: 0,
            eof,
            last: eof,
            nodes: 0,
            nesting: 0,
        })
    }

    pub fn kind(&mut self) -> Kind {
        self.tokens
            .get(self.next)
            .map_or(Kind::End, |token| token.kind)
    }

    /// Bounded parse-position snapshot for the single set-group alternative
    /// in `atom`: restoring rewinds only the token index and last-span, never
    /// node budgets or the depth guard, so speculative work stays charged.
    pub fn snapshot(&self) -> (usize, SourceSpan) {
        (self.next, self.last)
    }

    pub fn restore(&mut self, saved: (usize, SourceSpan)) {
        self.next = saved.0;
        self.last = saved.1;
    }

    pub fn position(&mut self) -> SourceSpan {
        self.tokens
            .get(self.next)
            .map_or(self.eof, |token| token.span)
    }

    pub fn take(&mut self) -> ParseResult<Token<'s>> {
        match self.tokens.get(self.next) {
            Some(token) => {
                let token = token.clone();
                self.next += 1;
                self.last = token.span;
                Ok(token)
            }
            None => Err(self.expected("token", "Complete the declaration or expression.")),
        }
    }

    pub fn expect(&mut self, kind: Kind) -> ParseResult<Token<'s>> {
        if self.kind() == kind {
            self.take()
        } else {
            Err(self.expected(kind.description(), "Use the required token at this position; header order and delimiters are significant."))
        }
    }

    pub fn eat(&mut self, kind: Kind) -> ParseResult<bool> {
        if self.kind() != kind {
            return Ok(false);
        }
        self.take()?;
        Ok(true)
    }

    pub fn name(&mut self) -> ParseResult<Name<'s>> {
        self.charge()?;
        let token = self.expect(Kind::Ident)?;
        Ok(Name {
            text: token.lexeme,
            span: token.span,
        })
    }

    pub fn text(&mut self) -> ParseResult<Text<'s>> {
        self.charge()?;
        let token = self.expect(Kind::String)?;
        let value = token
            .text
            .ok_or_else(|| Self::invariant("String token has no decoded value"))?;
        Ok(Text {
            value,
            span: token.span,
        })
    }

    pub fn cover(&self, start: SourceSpan, end: SourceSpan) -> ParseResult<SourceSpan> {
        start
            .cover(end, self.source)
            .map_err(|_| Self::invariant("Invalid parser source span"))
    }

    pub fn expected(&mut self, expected: &str, help: &str) -> Box<Diagnostic> {
        let span = self.position();
        let actual = match self.tokens.get(self.next) {
            Some(token) => format!("{} {:?}", token.kind.description(), token.lexeme),
            None => "end of source".into(),
        };
        let mut error = Diagnostic::new(
            Code::UnexpectedToken,
            Phase::Parse,
            format!("Expected {expected}"),
            Some(span),
        );
        error.expected = Some(expected.into());
        error.actual = Some(actual.into_boxed_str());
        error.help = Some(help.into());
        Box::new(error)
    }

    pub fn invariant(message: &str) -> Box<Diagnostic> {
        let mut error = Diagnostic::new(Code::InvalidProgram, Phase::Parse, message, None);
        error.help = Some("Report this internal source-AST invariant failure.".into());
        Box::new(error)
    }

    pub fn charge(&mut self) -> ParseResult<()> {
        if self.nodes >= self.limits.nodes {
            let span = self.position();
            return Err(self.limit(span, "Source AST node budget exhausted", self.limits.nodes,
                format!("{} source AST nodes already admitted; another node is required", self.nodes),
                "Reduce declarations, values, paths or expressions, or request a larger node budget."));
        }
        self.nodes += 1;
        Ok(())
    }

    pub fn depth(&self, depth: usize, span: SourceSpan) -> ParseResult<()> {
        let cap = self.limits.nesting.min(MAX_SOURCE_DEPTH);
        if depth > cap {
            Err(self.limit(span, "Source AST depth limit exceeded", cap,
                format!("intrinsic AST depth {depth}"),
                "Reduce nesting or split long connective chains into separate checks; the architectural cap cannot be overridden."))
        } else {
            Ok(())
        }
    }

    pub fn enter(&mut self) -> ParseResult<()> {
        let cap = self.limits.nesting.min(MAX_SOURCE_DEPTH);
        if self.nesting >= cap {
            let span = self.position();
            return Err(self.limit(span, "Parser recursion limit exceeded", cap,
                format!("recursive syntax depth {}", self.nesting + 1),
                "Reduce parentheses, negations, nested spreads or quantifiers; the architectural cap cannot be overridden."));
        }
        self.nesting += 1;
        Ok(())
    }

    pub fn leave(&mut self) {
        // Called exactly once after each successful enter, including error exits.
        self.nesting -= 1;
    }

    fn limit(
        &self,
        span: SourceSpan,
        message: &str,
        cap: usize,
        actual: String,
        help: &str,
    ) -> Box<Diagnostic> {
        let mut error = Diagnostic::new(Code::LimitExceeded, Phase::Parse, message, Some(span));
        error.expected = Some(format!("at most {cap}").into_boxed_str());
        error.actual = Some(actual.into_boxed_str());
        error.help = Some(help.into());
        Box::new(error)
    }
}

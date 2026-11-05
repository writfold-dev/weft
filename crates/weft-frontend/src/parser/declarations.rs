use super::{ParseResult, Parser, cursor::Cursor};
use crate::{
    ast::{Header, Statement},
    lexer::Kind,
};
use weft_domain::DeclarationKind;

impl<'s> Cursor<'s, '_> {
    pub(super) fn header(&mut self) -> ParseResult<Header<'s>> {
        self.charge()?;
        let start = self.expect(Kind::Keyword("review"))?.span;
        let name = self.name()?;
        self.expect(Kind::LeftBrace)?;
        self.expect(Kind::Keyword("context"))?;
        let context = self.text()?;
        self.expect(Kind::Keyword("at"))?;
        let snapshot = self.text()?;
        self.expect(Kind::Semicolon)?;
        self.expect(Kind::Keyword("profile"))?;
        let profile = self.text()?;
        self.expect(Kind::Semicolon)?;
        self.expect(Kind::Keyword("target"))?;
        let target = self.name()?;
        self.expect(Kind::Assign)?;
        self.expect(Kind::Keyword("proposal"))?;
        let proposal = self.text()?;
        let end = self.expect(Kind::Semicolon)?.span;
        Ok(Header {
            name,
            context,
            snapshot,
            profile,
            target,
            proposal,
            span: self.cover(start, end)?,
        })
    }
}

impl<'s> Parser<'s, '_> {
    pub(super) fn statements(&mut self) -> ParseResult<()> {
        while self.cursor.kind() != Kind::RightBrace {
            self.cursor.charge()?;
            let statement = self.statement()?;
            self.ast.statements.push(statement);
        }
        self.cursor.expect(Kind::RightBrace)?;
        if self.cursor.kind() != Kind::End {
            return Err(self.cursor.expected(
                "end of source",
                "A source file contains exactly one review.",
            ));
        }
        Ok(())
    }

    fn statement(&mut self) -> ParseResult<Statement<'s>> {
        match self.cursor.kind() {
            Kind::Keyword("claim") => self.binding(DeclarationKind::Claim),
            Kind::Keyword("asset") => self.binding(DeclarationKind::Asset),
            Kind::Keyword("rule") => self.binding(DeclarationKind::Rule),
            Kind::Keyword("need") => self.need(),
            Kind::Keyword("assume") => self.proposition(false),
            Kind::Keyword("check") => self.proposition(true),
            Kind::Ident => self.set_binding(),
            _ => Err(self.cursor.expected("claim, asset, rule, set binding, need, assume, check or }",
                "Place context/profile/target once in header order; bind sets with name := set, not let.")),
        }
    }

    fn binding(&mut self, kind: DeclarationKind) -> ParseResult<Statement<'s>> {
        let start = self.cursor.take()?.span;
        let name = self.cursor.name()?;
        self.cursor.expect(Kind::Assign)?;
        self.cursor.expect(Kind::Keyword("citation"))?;
        let citation = self.cursor.text()?;
        let end = self.cursor.expect(Kind::Semicolon)?.span;
        Ok(Statement::Binding {
            kind,
            name,
            citation,
            span: self.cursor.cover(start, end)?,
        })
    }

    fn need(&mut self) -> ParseResult<Statement<'s>> {
        let start = self.cursor.take()?.span;
        let name = self.cursor.name()?;
        let end = self.cursor.expect(Kind::Semicolon)?.span;
        Ok(Statement::Need {
            name,
            span: self.cursor.cover(start, end)?,
        })
    }

    fn set_binding(&mut self) -> ParseResult<Statement<'s>> {
        let name = self.cursor.name()?;
        self.cursor.expect(Kind::Bind)?;
        let value = self.set_expression()?;
        let end = self.cursor.expect(Kind::Semicolon)?.span;
        Ok(Statement::Set {
            name,
            value,
            span: self.cursor.cover(name.span, end)?,
        })
    }

    fn proposition(&mut self, check: bool) -> ParseResult<Statement<'s>> {
        let start = self.cursor.take()?.span;
        let name = self.cursor.name()?;
        self.cursor.expect(Kind::Colon)?;
        let expression = self.expression()?;
        let mut rules = Vec::new();
        if check && self.cursor.eat(Kind::Keyword("by"))? {
            rules.push(self.cursor.name()?);
            while self.cursor.eat(Kind::Comma)? {
                rules.push(self.cursor.name()?);
            }
        }
        let end = self.cursor.expect(Kind::Semicolon)?.span;
        let span = self.cursor.cover(start, end)?;
        if check {
            Ok(Statement::Check {
                name,
                expression,
                rules,
                span,
            })
        } else {
            Ok(Statement::Assume {
                name,
                expression,
                span,
            })
        }
    }
}

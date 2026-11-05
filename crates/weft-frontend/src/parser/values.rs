use super::{ParseResult, Parser};
use crate::{
    ast::{Comparable, Name, Path, SetExprId, SetItem, SetKind, Value},
    lexer::Kind,
};
use weft_domain::SourceSpan;

impl<'s> Parser<'s, '_> {
    pub(super) fn value(&mut self) -> ParseResult<Value<'s>> {
        match self.cursor.kind() {
            Kind::Ident => {
                let root = self.cursor.name()?;
                Ok(Value::Path(self.path(root)?))
            }
            Kind::String => Ok(Value::Text(self.cursor.text()?)),
            Kind::Natural => {
                self.cursor.charge()?;
                let token = self.cursor.take()?;
                Ok(Value::Natural(token.lexeme, token.span))
            }
            Kind::Keyword("true" | "false") => {
                self.cursor.charge()?;
                let token = self.cursor.take()?;
                Ok(Value::Boolean(token.kind == Kind::Keyword("true"), token.span))
            }
            _ => Err(self.cursor.expected("scalar value or field path",
                "Use a string, natural, Boolean or name.path; calls and native sets are not scalar arguments or members.")),
        }
    }

    pub(super) fn path(&mut self, root: Name<'s>) -> ParseResult<Path<'s>> {
        let mut fields = Vec::new();
        let mut end = root.span;
        while self.cursor.eat(Kind::Dot)? {
            let field = self.cursor.name()?;
            end = field.span;
            fields.push(field);
        }
        Ok(Path {
            root,
            fields,
            span: self.cursor.cover(root.span, end)?,
        })
    }

    pub(super) fn comparable(&mut self) -> ParseResult<Comparable<'s>> {
        if self.cursor.kind() == Kind::LeftBrace {
            Ok(Comparable::Set(self.set_expression()?))
        } else {
            Ok(Comparable::Value(self.value()?))
        }
    }

    pub(super) fn comparable_shape(
        &self,
        value: &Comparable<'s>,
    ) -> ParseResult<(SourceSpan, usize)> {
        match value {
            Comparable::Value(value) => Ok((value.span(), 1)),
            Comparable::Set(id) => {
                let set = self.set(*id)?;
                Ok((set.span, set.depth))
            }
        }
    }

    pub(super) fn set_expression(&mut self) -> ParseResult<SetExprId> {
        self.cursor.enter()?;
        let result = self.set_inner();
        self.cursor.leave();
        result
    }

    fn set_inner(&mut self) -> ParseResult<SetExprId> {
        self.cursor.charge()?;
        match self.cursor.kind() {
            Kind::Ident => {
                let root = self.cursor.name()?;
                let path = self.path(root)?;
                let span = path.span;
                self.push_set(SetKind::Path(path), span, 1)
            }
            Kind::LeftBrace => self.set_literal(),
            _ => Err(self.cursor.expected(
                "set literal or field path",
                "Write {value, ...other_set,} or a previously bound set path.",
            )),
        }
    }

    fn set_literal(&mut self) -> ParseResult<SetExprId> {
        let start = self.cursor.expect(Kind::LeftBrace)?.span;
        let mut items = Vec::new();
        let mut depth = 1;
        while self.cursor.kind() != Kind::RightBrace {
            let (item, child_depth) = if self.cursor.kind() == Kind::Spread {
                self.cursor.charge()?;
                let spread_start = self.cursor.take()?.span;
                let set = self.set_expression()?;
                let nested = self.set(set)?;
                let span = self.cursor.cover(spread_start, nested.span)?;
                (SetItem::Spread(set, span), nested.depth)
            } else {
                (SetItem::Value(self.value()?), 1)
            };
            depth = depth.max(child_depth + 1);
            self.cursor
                .depth(depth, self.cursor.cover(start, self.cursor.last)?)?;
            items.push(item);
            if !self.cursor.eat(Kind::Comma)? {
                break;
            }
        }
        let end = self.cursor.expect(Kind::RightBrace)?.span;
        self.push_set(
            SetKind::Literal(items),
            self.cursor.cover(start, end)?,
            depth,
        )
    }
}

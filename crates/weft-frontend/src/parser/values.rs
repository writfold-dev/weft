use super::{ParseResult, Parser};
use crate::{
    ast::{Comparable, Name, Path, SetExprId, SetItem, SetKind, Value},
    lexer::Kind,
};
use weft_domain::{SetOperation, SourceSpan};

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

    /// One operand of a comparison: a full set-algebra expression when the
    /// source is set-led, or a scalar value otherwise. A bare path without a
    /// following set operator stays scalar and is reclassified by typing.
    pub(super) fn comparable(&mut self) -> ParseResult<Comparable<'s>> {
        match self.cursor.kind() {
            Kind::LeftBrace => Ok(Comparable::Set(self.set_expression()?)),
            Kind::LeftParen => {
                let start = self.cursor.expect(Kind::LeftParen)?.span;
                let inner = self.set_expression()?;
                let end = self.cursor.expect(Kind::RightParen)?.span;
                let span = self.cursor.cover(start, end)?;
                self.cursor.depth(self.set(inner)?.depth, span)?;
                Ok(Comparable::Set(inner))
            }
            Kind::Ident => {
                let root = self.cursor.name()?;
                let path = self.path(root)?;
                self.comparable_after_path(path)
            }
            _ => Ok(Comparable::Value(self.value()?)),
        }
    }

    /// Continue from an already-parsed leading path: a following set
    /// operator makes it the left operand of an operator chain; otherwise it
    /// stays a scalar path that typing may reclassify as a set.
    pub(super) fn comparable_after_path(&mut self, path: Path<'s>) -> ParseResult<Comparable<'s>> {
        if matches!(
            self.cursor.kind(),
            Kind::Pipe | Kind::Ampersand | Kind::Minus
        ) {
            let span = path.span;
            let id = self.push_set(SetKind::Path(path), span, 1)?;
            Ok(Comparable::Set(self.set_chain(id)?))
        } else {
            Ok(Comparable::Value(Value::Path(path)))
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
        self.set_alternation()
    }

    /// `|` and `-` share one precedence level and associate left:
    /// `a | b - c` means `(a | b) - c`.
    fn set_alternation(&mut self) -> ParseResult<SetExprId> {
        let mut left = self.set_intersection()?;
        loop {
            let operation = match self.cursor.kind() {
                Kind::Pipe => SetOperation::Union,
                Kind::Minus => SetOperation::Difference,
                _ => break,
            };
            self.cursor.take()?;
            let right = self.set_intersection()?;
            let (span, depth) = self.binary_shape(left, right)?;
            left = self.push_set(
                SetKind::Binary {
                    operation,
                    left,
                    right,
                },
                span,
                depth,
            )?;
        }
        Ok(left)
    }

    /// `&` binds tighter than `|`/`-`: `a | b & c` means `a | (b & c)`.
    fn set_intersection(&mut self) -> ParseResult<SetExprId> {
        let mut left = self.set_atom()?;
        while self.cursor.kind() == Kind::Ampersand {
            self.cursor.take()?;
            let right = self.set_atom()?;
            let (span, depth) = self.binary_shape(left, right)?;
            left = self.push_set(
                SetKind::Binary {
                    operation: SetOperation::Intersection,
                    left,
                    right,
                },
                span,
                depth,
            )?;
        }
        Ok(left)
    }

    fn set_atom(&mut self) -> ParseResult<SetExprId> {
        match self.cursor.kind() {
            Kind::Ident => {
                let root = self.cursor.name()?;
                let path = self.path(root)?;
                let span = path.span;
                self.push_set(SetKind::Path(path), span, 1)
            }
            Kind::LeftBrace => self.set_literal(),
            Kind::LeftParen => {
                let start = self.cursor.expect(Kind::LeftParen)?.span;
                let inner = self.set_expression()?;
                let end = self.cursor.expect(Kind::RightParen)?.span;
                let span = self.cursor.cover(start, end)?;
                self.cursor.depth(self.set(inner)?.depth, span)?;
                Ok(inner)
            }
            _ => Err(self.cursor.expected(
                "set literal, set path or parenthesized set expression",
                "Write {value, ...other_set}, a set path, operators (|, &, -) over sets, or parenthesized set expressions.",
            )),
        }
    }

    /// Continue an operator chain from an already-parsed leading set node.
    fn set_chain(&mut self, first: SetExprId) -> ParseResult<SetExprId> {
        let mut left = first;
        loop {
            let operation = match self.cursor.kind() {
                Kind::Pipe => SetOperation::Union,
                Kind::Ampersand => SetOperation::Intersection,
                Kind::Minus => SetOperation::Difference,
                _ => break,
            };
            self.cursor.take()?;
            let right = self.set_intersection()?;
            let (span, depth) = self.binary_shape(left, right)?;
            left = self.push_set(
                SetKind::Binary {
                    operation,
                    left,
                    right,
                },
                span,
                depth,
            )?;
        }
        Ok(left)
    }

    fn binary_shape(&self, left: SetExprId, right: SetExprId) -> ParseResult<(SourceSpan, usize)> {
        let left = self.set(left)?;
        let right = self.set(right)?;
        let span = self.cursor.cover(left.span, right.span)?;
        Ok((span, left.depth.max(right.depth) + 1))
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

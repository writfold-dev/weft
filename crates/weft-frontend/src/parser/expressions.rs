use super::{ParseResult, Parser, cursor::Cursor};
use crate::{
    ast::{Comparable, ExprId, ExprKind, Name, Value},
    lexer::Kind,
};
use weft_domain::{Comparison, QuantifierKind};

impl<'s> Parser<'s, '_> {
    pub(super) fn expression(&mut self) -> ParseResult<ExprId> {
        self.cursor.enter()?;
        let result = self.disjunction();
        self.cursor.leave();
        result
    }

    fn disjunction(&mut self) -> ParseResult<ExprId> {
        let mut left = self.conjunction()?;
        while self.cursor.eat(Kind::Keyword("or"))? {
            let right = self.conjunction()?;
            left = self.connective(left, right, false)?;
        }
        Ok(left)
    }

    fn conjunction(&mut self) -> ParseResult<ExprId> {
        let mut left = self.negation()?;
        while self.cursor.eat(Kind::Keyword("and"))? {
            let right = self.negation()?;
            left = self.connective(left, right, true)?;
        }
        Ok(left)
    }

    fn connective(&mut self, left: ExprId, right: ExprId, and: bool) -> ParseResult<ExprId> {
        let left_node = self.expr(left)?;
        let right_node = self.expr(right)?;
        let span = self.cursor.cover(left_node.span, right_node.span)?;
        let depth = left_node.depth.max(right_node.depth) + 1;
        let kind = if and {
            ExprKind::And(left, right)
        } else {
            ExprKind::Or(left, right)
        };
        self.push_expr(kind, span, depth)
    }

    fn negation(&mut self) -> ParseResult<ExprId> {
        if self.cursor.kind() != Kind::Keyword("not") {
            return self.atom();
        }
        let start = self.cursor.take()?.span;
        self.cursor.enter()?;
        let result = self.negation();
        self.cursor.leave();
        let child = result?;
        let expression = self.expr(child)?;
        let span = self.cursor.cover(start, expression.span)?;
        let depth = expression.depth + 1;
        self.push_expr(ExprKind::Not(child), span, depth)
    }

    fn atom(&mut self) -> ParseResult<ExprId> {
        match self.cursor.kind() {
            Kind::LeftParen => self.group(),
            Kind::Keyword("forall") => self.quantifier(QuantifierKind::Forall),
            Kind::Keyword("exists") => self.quantifier(QuantifierKind::Exists),
            Kind::Ident => {
                let name = self.cursor.name()?;
                if self.cursor.kind() == Kind::LeftParen { self.predicate(name) }
                else {
                    let path = self.path(name)?;
                    self.comparison(Comparable::Value(Value::Path(path)))
                }
            }
            Kind::LeftBrace | Kind::String | Kind::Natural | Kind::Keyword("true" | "false") => {
                let left = self.comparable()?;
                self.comparison(left)
            }
            _ => Err(self.cursor.expected("proposition",
                "Use a Boolean, comparison, predicate call, quantifier or parenthesized proposition; bare names are not propositions.")),
        }
    }

    fn group(&mut self) -> ParseResult<ExprId> {
        let start = self.cursor.expect(Kind::LeftParen)?.span;
        let expression = self.expression()?;
        let end = self.cursor.expect(Kind::RightParen)?.span;
        let span = self.cursor.cover(start, end)?;
        self.ast
            .expression_mut(expression)
            .ok_or_else(|| Cursor::invariant("Missing grouped source expression"))?
            .span = span;
        Ok(expression)
    }

    fn comparison(&mut self, left: Comparable<'s>) -> ParseResult<ExprId> {
        let operation = match self.cursor.kind() {
            Kind::Equal => Comparison::Equal,
            Kind::NotEqual => Comparison::NotEqual,
            _ => {
                if let Comparable::Value(Value::Boolean(value, span)) = left {
                    return self.push_expr(ExprKind::Boolean(value), span, 1);
                }
                return Err(self.cursor.expected("== or !=",
                    "Compare two scalar values or sets; a bare value/path/set is not a proposition."));
            }
        };
        self.cursor.take()?;
        let right = self.comparable()?;
        if matches!(self.cursor.kind(), Kind::Equal | Kind::NotEqual) {
            return Err(self.cursor.expected(
                "Boolean connective or end of proposition",
                "Comparisons cannot chain; write a == b and b == c instead.",
            ));
        }
        let (left_span, left_depth) = self.comparable_shape(&left)?;
        let (right_span, right_depth) = self.comparable_shape(&right)?;
        let span = self.cursor.cover(left_span, right_span)?;
        self.push_expr(
            ExprKind::Compare {
                operation,
                left,
                right,
            },
            span,
            left_depth.max(right_depth) + 1,
        )
    }

    fn predicate(&mut self, name: Name<'s>) -> ParseResult<ExprId> {
        self.cursor.expect(Kind::LeftParen)?;
        let mut arguments = Vec::new();
        if self.cursor.kind() != Kind::RightParen {
            arguments.push(self.value()?);
            while self.cursor.eat(Kind::Comma)? {
                arguments.push(self.value()?);
            }
        }
        let end = self.cursor.expect(Kind::RightParen)?.span;
        let span = self.cursor.cover(name.span, end)?;
        let depth = if arguments.is_empty() { 1 } else { 2 };
        self.push_expr(ExprKind::Predicate { name, arguments }, span, depth)
    }

    fn quantifier(&mut self, kind: QuantifierKind) -> ParseResult<ExprId> {
        let start = self.cursor.take()?.span;
        let binder = self.cursor.name()?;
        self.cursor.expect(Kind::Keyword("in"))?;
        let domain = self.set_expression()?;
        self.cursor.expect(Kind::LeftBrace)?;
        let body = self.expression()?;
        let end = self.cursor.expect(Kind::RightBrace)?.span;
        let depth = self.set(domain)?.depth.max(self.expr(body)?.depth) + 1;
        self.push_expr(
            ExprKind::Quantifier {
                kind,
                binder,
                domain,
                body,
            },
            self.cursor.cover(start, end)?,
            depth,
        )
    }
}

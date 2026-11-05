mod cursor;
mod declarations;
mod expressions;
#[cfg(test)]
mod limits_tests;
#[cfg(test)]
mod tests;
mod values;

use crate::{
    ast::{Expr, ExprId, ExprKind, Parsed, SetExpr, SetExprId, SetKind},
    lexer,
};
use cursor::Cursor;
use weft_domain::{Diagnostic, Limits, SourceSpan};

type ParseResult<T> = Result<T, Box<Diagnostic>>;

pub(crate) fn parse<'s>(source: &'s str, limits: &Limits) -> Result<Parsed<'s>, Vec<Diagnostic>> {
    parse_source(source, limits).map_err(|error| vec![*error])
}

fn parse_source<'s>(source: &'s str, limits: &Limits) -> ParseResult<Parsed<'s>> {
    let tokens = lexer::lex(source, limits)?;
    let mut cursor = Cursor::new(source, limits, tokens)?;
    let header = cursor.header()?;
    let mut parser = Parser {
        cursor,
        ast: Parsed::new(header),
    };
    parser.statements()?;
    Ok(parser.ast)
}

struct Parser<'s, 'l> {
    cursor: Cursor<'s, 'l>,
    ast: Parsed<'s>,
}

impl<'s> Parser<'s, '_> {
    fn push_expr(
        &mut self,
        kind: ExprKind<'s>,
        span: SourceSpan,
        depth: usize,
    ) -> ParseResult<ExprId> {
        self.cursor.depth(depth, span)?;
        self.cursor.charge()?;
        Ok(self.ast.push_expr(Expr { kind, span, depth }))
    }

    fn push_set(
        &mut self,
        kind: SetKind<'s>,
        span: SourceSpan,
        depth: usize,
    ) -> ParseResult<SetExprId> {
        self.cursor.depth(depth, span)?;
        // The set node is charged before parsing/allocating its children.
        Ok(self.ast.push_set(SetExpr { kind, span, depth }))
    }

    fn expr(&self, id: ExprId) -> ParseResult<&Expr<'s>> {
        self.ast
            .expression(id)
            .ok_or_else(|| Cursor::invariant("Missing source expression"))
    }

    fn set(&self, id: SetExprId) -> ParseResult<&SetExpr<'s>> {
        self.ast
            .set(id)
            .ok_or_else(|| Cursor::invariant("Missing source set expression"))
    }
}

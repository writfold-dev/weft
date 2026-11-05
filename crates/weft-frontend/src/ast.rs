use std::borrow::Cow;
use weft_domain::{Comparison, DeclarationKind, QuantifierKind, SourceSpan};

#[derive(Clone, Copy, Debug)]
pub(crate) struct Name<'s> {
    pub text: &'s str,
    pub span: SourceSpan,
}
#[derive(Clone, Debug)]
pub(crate) struct Text<'s> {
    pub value: Cow<'s, str>,
    pub span: SourceSpan,
}
#[derive(Clone, Debug)]
pub(crate) struct Header<'s> {
    pub name: Name<'s>,
    pub context: Text<'s>,
    pub snapshot: Text<'s>,
    pub profile: Text<'s>,
    pub target: Name<'s>,
    pub proposal: Text<'s>,
    pub span: SourceSpan,
}
#[derive(Clone, Debug)]
pub(crate) struct Path<'s> {
    pub root: Name<'s>,
    pub fields: Vec<Name<'s>>,
    pub span: SourceSpan,
}
#[derive(Clone, Debug)]
pub(crate) enum Value<'s> {
    Boolean(bool, SourceSpan),
    Natural(&'s str, SourceSpan),
    Text(Text<'s>),
    Path(Path<'s>),
}
impl Value<'_> {
    pub fn span(&self) -> SourceSpan {
        match self {
            Self::Boolean(_, span) | Self::Natural(_, span) => *span,
            Self::Text(text) => text.span,
            Self::Path(path) => path.span,
        }
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct ExprId(usize);
impl ExprId {
    pub fn index(self) -> usize {
        self.0
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct SetExprId(usize);
impl SetExprId {
    pub fn index(self) -> usize {
        self.0
    }
}
#[derive(Clone, Debug)]
pub(crate) enum Comparable<'s> {
    Value(Value<'s>),
    Set(SetExprId),
}
#[derive(Clone, Debug)]
pub(crate) enum ExprKind<'s> {
    Boolean(bool),
    Not(ExprId),
    And(ExprId, ExprId),
    Or(ExprId, ExprId),
    Compare {
        operation: Comparison,
        left: Comparable<'s>,
        right: Comparable<'s>,
    },
    Predicate {
        name: Name<'s>,
        arguments: Vec<Value<'s>>,
    },
    Quantifier {
        kind: QuantifierKind,
        binder: Name<'s>,
        domain: SetExprId,
        body: ExprId,
    },
}
#[derive(Clone, Debug)]
pub(crate) struct Expr<'s> {
    pub kind: ExprKind<'s>,
    pub span: SourceSpan,
    pub depth: usize,
}
#[derive(Clone, Debug)]
pub(crate) enum SetItem<'s> {
    Value(Value<'s>),
    Spread(SetExprId, SourceSpan),
}
#[derive(Clone, Debug)]
pub(crate) enum SetKind<'s> {
    Literal(Vec<SetItem<'s>>),
    Path(Path<'s>),
}
#[derive(Clone, Debug)]
pub(crate) struct SetExpr<'s> {
    pub kind: SetKind<'s>,
    pub span: SourceSpan,
    pub depth: usize,
}
#[derive(Clone, Debug)]
pub(crate) enum Statement<'s> {
    Binding {
        kind: DeclarationKind,
        name: Name<'s>,
        citation: Text<'s>,
        span: SourceSpan,
    },
    Set {
        name: Name<'s>,
        value: SetExprId,
        span: SourceSpan,
    },
    Need {
        name: Name<'s>,
        span: SourceSpan,
    },
    Assume {
        name: Name<'s>,
        expression: ExprId,
        span: SourceSpan,
    },
    Check {
        name: Name<'s>,
        expression: ExprId,
        rules: Vec<Name<'s>>,
        span: SourceSpan,
    },
}
#[derive(Debug)]
pub(crate) struct Parsed<'s> {
    pub header: Header<'s>,
    pub statements: Vec<Statement<'s>>,
    expressions: Vec<Expr<'s>>,
    sets: Vec<SetExpr<'s>>,
}
impl<'s> Parsed<'s> {
    pub fn new(header: Header<'s>) -> Self {
        Self {
            header,
            statements: Vec::new(),
            expressions: Vec::new(),
            sets: Vec::new(),
        }
    }
    // Only the bounded parser allocates source-AST identifiers. The AST is not
    // the validated runtime IR and is never accepted directly by the kernel.
    pub fn push_expr(&mut self, expr: Expr<'s>) -> ExprId {
        let id = ExprId(self.expressions.len());
        self.expressions.push(expr);
        id
    }
    pub fn push_set(&mut self, expr: SetExpr<'s>) -> SetExprId {
        let id = SetExprId(self.sets.len());
        self.sets.push(expr);
        id
    }
    pub fn expression(&self, id: ExprId) -> Option<&Expr<'s>> {
        self.expressions.get(id.index())
    }
    pub fn expression_mut(&mut self, id: ExprId) -> Option<&mut Expr<'s>> {
        self.expressions.get_mut(id.index())
    }
    pub fn set(&self, id: SetExprId) -> Option<&SetExpr<'s>> {
        self.sets.get(id.index())
    }
}

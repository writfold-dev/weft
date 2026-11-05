use syn::visit::{self, Visit};

// This recognizes projections of existing values, not arbitrary functions with
// receivers. Calls that manufacture a nominal value are checked separately.
// Field-rooted lookup/copy chains still rely on Rust's type checking; syntax
// alone cannot prove the semantics of an overloaded method or dereference.
pub(super) fn returned(signature: &syn::Signature, body: &syn::Block) -> bool {
    let mut values = Existing {
        signature,
        bindings: Vec::new(),
        returns_existing: true,
    };
    let returned = values.block(body);
    values.returns_existing && returned
}

struct Existing<'a> {
    signature: &'a syn::Signature,
    bindings: Vec<(&'a syn::Pat, bool)>,
    returns_existing: bool,
}

impl<'a> Existing<'a> {
    fn block(&mut self, block: &'a syn::Block) -> bool {
        let prior = self.bindings.len();
        let result = if let Some((last, earlier)) = block.stmts.split_last() {
            for statement in earlier {
                self.visit_stmt(statement);
            }
            match last {
                syn::Stmt::Expr(expr, _) => self.value(expr),
                _ => false,
            }
        } else {
            false
        };
        self.bindings.truncate(prior);
        result
    }

    fn value(&mut self, expr: &'a syn::Expr) -> bool {
        match expr {
            syn::Expr::Field(field) => self.value(&field.base),
            syn::Expr::Reference(reference) => self.value(&reference.expr),
            syn::Expr::Unary(unary) if matches!(unary.op, syn::UnOp::Deref(_)) => {
                self.value(&unary.expr)
            }
            syn::Expr::Paren(paren) => self.value(&paren.expr),
            syn::Expr::Group(group) => self.value(&group.expr),
            syn::Expr::Block(block) => self.block(&block.block),
            syn::Expr::Return(ret) => {
                let existing = ret.expr.as_ref().is_some_and(|expr| self.value(expr));
                self.returns_existing &= existing;
                existing
            }
            syn::Expr::Path(path) => path.path.get_ident().is_some_and(|ident| {
                if ident == "self" {
                    return true;
                }
                if let Some((_, existing)) = self
                    .bindings
                    .iter()
                    .rev()
                    .find(|(pat, _)| binds(pat, ident))
                {
                    return *existing;
                }
                self.signature
                    .inputs
                    .iter()
                    .any(|arg| matches!(arg, syn::FnArg::Typed(arg) if binds(&arg.pat, ident)))
            }),
            syn::Expr::Call(call) => {
                matches!(call.func.as_ref(), syn::Expr::Path(path)
                if path.path.segments.last().is_some_and(|segment| {
                    matches!(segment.ident.to_string().as_str(), "Some" | "Ok")
                })) && call.args.iter().all(|arg| self.value(arg))
            }
            syn::Expr::MethodCall(call) => {
                matches!(
                    call.method.to_string().as_str(),
                    "get" | "find" | "copied" | "cloned" | "clone"
                ) && self.value(&call.receiver)
            }
            syn::Expr::Match(value) if self.value(&value.expr) => value.arms.iter().all(|arm| {
                self.bindings.push((&arm.pat, true));
                let existing = self.value(&arm.body);
                self.bindings.pop();
                existing
            }),
            _ => false,
        }
    }
}

impl<'ast> Visit<'ast> for Existing<'ast> {
    fn visit_block(&mut self, node: &'ast syn::Block) {
        self.block(node);
    }

    fn visit_local(&mut self, node: &'ast syn::Local) {
        let immutable = matches!(&node.pat, syn::Pat::Ident(binding)
            if binding.mutability.is_none() && binding.subpat.is_none());
        let existing = immutable
            && node
                .init
                .as_ref()
                .is_some_and(|init| self.value(&init.expr));
        visit::visit_local(self, node);
        self.bindings.push((&node.pat, existing));
    }

    fn visit_expr_return(&mut self, node: &'ast syn::ExprReturn) {
        self.returns_existing &= node.expr.as_ref().is_some_and(|expr| self.value(expr));
        visit::visit_expr_return(self, node);
    }

    fn visit_expr_closure(&mut self, _: &'ast syn::ExprClosure) {}
    fn visit_item_fn(&mut self, _: &'ast syn::ItemFn) {}
}

fn binds(pattern: &syn::Pat, ident: &syn::Ident) -> bool {
    match pattern {
        syn::Pat::Ident(binding) => binding.ident == *ident,
        syn::Pat::Reference(reference) => binds(&reference.pat, ident),
        syn::Pat::TupleStruct(tuple) => tuple.elems.iter().any(|pat| binds(pat, ident)),
        syn::Pat::Tuple(tuple) => tuple.elems.iter().any(|pat| binds(pat, ident)),
        syn::Pat::Struct(value) => value.fields.iter().any(|field| binds(&field.pat, ident)),
        syn::Pat::Or(value) => value.cases.iter().all(|pat| binds(pat, ident)),
        _ => false,
    }
}

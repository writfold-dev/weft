use syn::visit::{self, Visit};

// Evidence of validation shape is deliberately not a proof of validation
// semantics. A delegated call must return the declared Result (compiler checked),
// but this pass cannot prove that its implementation validates the raw input.
pub(super) fn fallible(body: &syn::Block) -> bool {
    let mut fallibility = Fallibility(false);
    fallibility.visit_block(body);
    fallibility.0 || matches!(body.stmts.last(), Some(syn::Stmt::Expr(expr, _)) if delegated(expr))
}

fn delegated(expr: &syn::Expr) -> bool {
    match expr {
        syn::Expr::Call(call) => matches!(call.func.as_ref(), syn::Expr::Path(path)
        if path.path.segments.last().is_some_and(|segment| {
            !matches!(segment.ident.to_string().as_str(), "Ok" | "Err" | "Some" | "Self")
        })),
        syn::Expr::MethodCall(call) => match call.receiver.as_ref() {
            syn::Expr::Call(_) | syn::Expr::MethodCall(_) => delegated(&call.receiver),
            syn::Expr::Path(_) | syn::Expr::Field(_) => true,
            _ => false,
        },
        syn::Expr::Return(ret) => ret.expr.as_ref().is_some_and(|expr| delegated(expr)),
        syn::Expr::Paren(paren) => delegated(&paren.expr),
        syn::Expr::Group(group) => delegated(&group.expr),
        syn::Expr::Block(block) => {
            matches!(block.block.stmts.last(), Some(syn::Stmt::Expr(expr, _)) if delegated(expr))
        }
        _ => false,
    }
}

struct Fallibility(bool);

impl<'ast> Visit<'ast> for Fallibility {
    fn visit_expr_try(&mut self, _: &'ast syn::ExprTry) {
        self.0 = true;
    }

    fn visit_expr_if(&mut self, node: &'ast syn::ExprIf) {
        let mut errors = ErrorReturn(false);
        errors.visit_block(&node.then_branch);
        if let Some((_, branch)) = &node.else_branch {
            errors.visit_expr(branch);
        }
        self.0 |= errors.0;
        visit::visit_expr_if(self, node);
    }

    fn visit_expr_match(&mut self, node: &'ast syn::ExprMatch) {
        let mut errors = ErrorReturn(false);
        for arm in &node.arms {
            errors.visit_expr(&arm.body);
        }
        self.0 |= errors.0;
        visit::visit_expr_match(self, node);
    }

    fn visit_expr_closure(&mut self, _: &'ast syn::ExprClosure) {}
    fn visit_item_fn(&mut self, _: &'ast syn::ItemFn) {}
}

struct ErrorReturn(bool);

impl<'ast> Visit<'ast> for ErrorReturn {
    fn visit_expr_call(&mut self, node: &'ast syn::ExprCall) {
        if matches!(node.func.as_ref(), syn::Expr::Path(path)
            if path.path.segments.last().is_some_and(|segment| segment.ident == "Err"))
        {
            self.0 = true;
        }
        visit::visit_expr_call(self, node);
    }

    fn visit_expr_closure(&mut self, _: &'ast syn::ExprClosure) {}
    fn visit_item_fn(&mut self, _: &'ast syn::ItemFn) {}
}

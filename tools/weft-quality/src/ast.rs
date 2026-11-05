use crate::{Policy, Report, Severity, lines::CodeLines};
use proc_macro2::{Delimiter, Span, TokenStream, TokenTree};
use syn::{
    spanned::Spanned,
    visit::{self, Visit},
};

pub(crate) fn forbids_unsafe(attributes: &[syn::Attribute]) -> bool {
    attributes.iter().any(|attribute| {
        if !matches!(attribute.style, syn::AttrStyle::Inner(_))
            || !attribute.path().is_ident("forbid")
        {
            return false;
        }
        attribute
            .parse_args_with(
                syn::punctuated::Punctuated::<syn::Path, syn::Token![,]>::parse_terminated,
            )
            .is_ok_and(|paths| paths.iter().any(|path| path.is_ident("unsafe_code")))
    })
}

pub(crate) fn check(
    policy: &Policy,
    path: &str,
    file: &syn::File,
    lines: &CodeLines<'_>,
    report: &mut Report,
) {
    let maximum = if policy.is_orchestration() { 250 } else { 400 };
    lines.record_file(path, maximum, report);
    AstCheck {
        path,
        lines,
        report,
        maximum,
    }
    .visit_file(file);
}

struct AstCheck<'a, 's> {
    path: &'a str,
    lines: &'a CodeLines<'s>,
    report: &'a mut Report,
    maximum: usize,
}

impl AstCheck<'_, '_> {
    fn error(&mut self, code: &str, span: Span, message: &str) {
        self.report
            .push(self.path, code, Severity::Error, span, message.into());
    }

    fn unsafe_token(&mut self, token: Option<syn::Token![unsafe]>) {
        if let Some(token) = token {
            self.error("WQ201", token.span(), "unsafe is prohibited");
        }
    }

    fn function(&mut self, name: &str, span: Span) {
        self.lines
            .record_span(self.path, "function", name, span, 80, self.report);
    }

    fn forbidden(&mut self, name: &str, span: Span) {
        let code = match name {
            "panic" | "panic_any" | "resume_unwind" | "unreachable" => "WQ202",
            "todo" => "WQ205",
            "unimplemented" => "WQ206",
            _ => return,
        };
        self.error(code, span, &format!("{name} is prohibited"));
    }

    fn macro_tokens(&mut self, tokens: TokenStream) {
        let mut iter = tokens.into_iter().peekable();
        while let Some(token) = iter.next() {
            match token {
                TokenTree::Group(group) => self.macro_tokens(group.stream()),
                TokenTree::Punct(punct) if punct.as_char() == '#' => {
                    if let Some(TokenTree::Group(group)) = iter.peek()
                        && group.delimiter() == Delimiter::Bracket
                    {
                        let mut attribute = group.stream().into_iter();
                        if let Some(TokenTree::Ident(ident)) = attribute.next()
                            && ident == "unsafe"
                            && matches!(attribute.next(), Some(TokenTree::Group(args))
                                if args.delimiter() == Delimiter::Parenthesis)
                        {
                            self.error("WQ201", ident.span(), "unsafe attributes are prohibited");
                        }
                    }
                }
                TokenTree::Ident(ident) => {
                    let next = iter.peek();
                    let unsafe_syntax = matches!(next, Some(TokenTree::Group(group))
                        if group.delimiter() == Delimiter::Brace)
                        || matches!(next, Some(TokenTree::Ident(word))
                            if word == "fn" || word == "impl" || word == "trait" || word == "extern");
                    if ident == "unsafe" && unsafe_syntax {
                        self.error("WQ201", ident.span(), "unsafe is prohibited");
                    }
                    let macro_call = matches!(next, Some(TokenTree::Punct(punct))
                        if punct.as_char() == '!');
                    let function_call = matches!(next, Some(TokenTree::Group(group))
                        if group.delimiter() == Delimiter::Parenthesis)
                        && (ident == "panic_any" || ident == "resume_unwind");
                    if macro_call || function_call {
                        self.forbidden(&ident.to_string(), ident.span());
                    }
                    if matches!(next, Some(TokenTree::Group(group))
                        if group.delimiter() == Delimiter::Parenthesis)
                    {
                        let code = match ident.to_string().as_str() {
                            "unwrap" | "unwrap_err" => Some("WQ203"),
                            "expect" | "expect_err" => Some("WQ204"),
                            _ => None,
                        };
                        if let Some(code) = code {
                            self.error(code, ident.span(),
                                "unwrap/expect call syntax in macros is prohibited; compiler typed-lint coverage does not include these expansions");
                        }
                    }
                }
                _ => {}
            }
        }
    }
}

impl<'ast> Visit<'ast> for AstCheck<'_, '_> {
    fn visit_item_fn(&mut self, node: &'ast syn::ItemFn) {
        self.function(&node.sig.ident.to_string(), node.span());
        visit::visit_item_fn(self, node);
    }

    fn visit_impl_item_fn(&mut self, node: &'ast syn::ImplItemFn) {
        self.function(&node.sig.ident.to_string(), node.span());
        visit::visit_impl_item_fn(self, node);
    }
    fn visit_attribute(&mut self, node: &'ast syn::Attribute) {
        if node.path().is_ident("unsafe") {
            self.error("WQ201", node.span(), "unsafe attributes are prohibited");
        }
        visit::visit_attribute(self, node);
    }

    fn visit_trait_item_fn(&mut self, node: &'ast syn::TraitItemFn) {
        if node.default.is_some() {
            self.function(&node.sig.ident.to_string(), node.span());
        }
        visit::visit_trait_item_fn(self, node);
    }

    fn visit_expr_closure(&mut self, node: &'ast syn::ExprClosure) {
        self.function("<closure>", node.span());
        visit::visit_expr_closure(self, node);
    }

    fn visit_item_mod(&mut self, node: &'ast syn::ItemMod) {
        if node.content.is_some() {
            self.lines.record_span(
                self.path,
                "module",
                &node.ident.to_string(),
                node.span(),
                self.maximum,
                self.report,
            );
        }
        visit::visit_item_mod(self, node);
    }

    fn visit_signature(&mut self, node: &'ast syn::Signature) {
        self.unsafe_token(node.unsafety);
        visit::visit_signature(self, node);
    }

    fn visit_expr_unsafe(&mut self, node: &'ast syn::ExprUnsafe) {
        self.unsafe_token(Some(node.unsafe_token));
        visit::visit_expr_unsafe(self, node);
    }

    fn visit_item_impl(&mut self, node: &'ast syn::ItemImpl) {
        self.unsafe_token(node.unsafety);
        visit::visit_item_impl(self, node);
    }

    fn visit_item_trait(&mut self, node: &'ast syn::ItemTrait) {
        self.unsafe_token(node.unsafety);
        visit::visit_item_trait(self, node);
    }

    fn visit_item_foreign_mod(&mut self, node: &'ast syn::ItemForeignMod) {
        self.unsafe_token(node.unsafety);
        visit::visit_item_foreign_mod(self, node);
    }

    fn visit_expr_call(&mut self, node: &'ast syn::ExprCall) {
        if let syn::Expr::Path(path) = node.func.as_ref()
            && let Some(segment) = path.path.segments.last()
        {
            self.forbidden(&segment.ident.to_string(), segment.ident.span());
        }
        visit::visit_expr_call(self, node);
    }

    // Macro input is not expanded Rust. Recognize only evident operation syntax;
    // the compiler's forbidden lints check actual types and macro expansions.
    fn visit_macro(&mut self, node: &'ast syn::Macro) {
        if let Some(segment) = node.path.segments.last() {
            self.forbidden(&segment.ident.to_string(), segment.ident.span());
        }
        self.macro_tokens(node.tokens.clone());
        visit::visit_macro(self, node);
    }
}

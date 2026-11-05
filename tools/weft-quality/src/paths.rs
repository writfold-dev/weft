mod rules;

use crate::{Policy, Report, Severity};
use std::collections::BTreeMap;
use syn::{
    spanned::Spanned,
    visit::{self, Visit},
};

pub(crate) struct PathCheck<'a> {
    policy: &'a Policy,
    path: &'a str,
    report: &'a mut Report,
    aliases: BTreeMap<String, Vec<String>>,
    test_context: bool,
}

impl<'a> PathCheck<'a> {
    pub(crate) fn new(policy: &'a Policy, path: &'a str, report: &'a mut Report) -> Self {
        Self {
            policy,
            path,
            report,
            aliases: BTreeMap::new(),
            test_context: policy.test_target,
        }
    }

    fn error(&mut self, code: &str, span: proc_macro2::Span, message: &str) {
        self.report
            .push(self.path, code, Severity::Error, span, message.into());
    }

    fn imports(&mut self, tree: &syn::UseTree, prefix: &mut Vec<String>) {
        match tree {
            syn::UseTree::Path(path) => {
                prefix.push(path.ident.to_string());
                self.imports(&path.tree, prefix);
                prefix.pop();
            }
            syn::UseTree::Group(group) => {
                for item in &group.items {
                    self.imports(item, prefix);
                }
            }
            syn::UseTree::Name(name) => {
                let mut full = prefix.clone();
                if name.ident != "self" {
                    full.push(name.ident.to_string());
                }
                let alias = full.last().cloned();
                self.inspect(&full, name.span());
                if let Some(alias) = alias {
                    self.aliases.insert(alias, full);
                }
            }
            syn::UseTree::Rename(rename) => {
                let mut full = prefix.clone();
                if rename.ident != "self" {
                    full.push(rename.ident.to_string());
                }
                self.inspect(&full, rename.span());
                self.aliases.insert(rename.rename.to_string(), full);
            }
            syn::UseTree::Glob(glob) => {
                self.inspect(prefix, glob.span());
                if prefix
                    .first()
                    .is_some_and(|root| !matches!(root.as_str(), "crate" | "super" | "self"))
                {
                    self.error(
                        "WQ405",
                        glob.span(),
                        "external glob imports obscure source boundary checks",
                    );
                }
            }
        }
    }

    fn macro_paths(&mut self, tokens: proc_macro2::TokenStream) {
        let mut parts = Vec::new();
        let mut start = None;
        for token in tokens {
            match token {
                proc_macro2::TokenTree::Ident(ident) => {
                    if start.is_none() {
                        start = Some(ident.span());
                    }
                    parts.push(ident.to_string());
                }
                proc_macro2::TokenTree::Punct(punct) if punct.as_char() == ':' => {}
                other => {
                    if let Some(span) = start.take() {
                        let call = matches!(&other, proc_macro2::TokenTree::Punct(punct) if punct.as_char() == '!')
                            || matches!(&other, proc_macro2::TokenTree::Group(group)
                                if group.delimiter() == proc_macro2::Delimiter::Parenthesis);
                        self.inspect_macro(&parts, span, call);
                    }
                    parts.clear();
                    if let proc_macro2::TokenTree::Group(group) = other {
                        self.macro_paths(group.stream());
                    }
                }
            }
        }
        if let Some(span) = start {
            self.inspect_macro(&parts, span, false);
        }
    }
}

impl<'ast> Visit<'ast> for PathCheck<'_> {
    fn visit_file(&mut self, node: &'ast syn::File) {
        for item in &node.items {
            if let syn::Item::Use(item) = item {
                self.visit_item_use(item);
            }
        }
        visit::visit_file(self, node);
    }

    fn visit_item_mod(&mut self, node: &'ast syn::ItemMod) {
        let previous = self.aliases.clone();
        let prior_test = self.test_context;
        self.test_context |= test_only(&node.attrs);
        if let Some((_, items)) = &node.content {
            for item in items {
                if let syn::Item::Use(item) = item {
                    self.visit_item_use(item);
                }
            }
        }
        visit::visit_item_mod(self, node);
        self.aliases = previous;
        self.test_context = prior_test;
    }

    fn visit_item_use(&mut self, node: &'ast syn::ItemUse) {
        let prior_test = self.test_context;
        self.test_context |= test_only(&node.attrs);
        self.imports(&node.tree, &mut Vec::new());
        self.test_context = prior_test;
    }

    fn visit_item_fn(&mut self, node: &'ast syn::ItemFn) {
        let prior_test = self.test_context;
        self.test_context |= test_only(&node.attrs);
        visit::visit_item_fn(self, node);
        self.test_context = prior_test;
    }

    fn visit_item_extern_crate(&mut self, node: &'ast syn::ItemExternCrate) {
        let name = node.ident.to_string();
        self.inspect(std::slice::from_ref(&name), node.span());
        if let Some((_, alias)) = &node.rename {
            self.aliases.insert(alias.to_string(), vec![name]);
        }
    }

    fn visit_path(&mut self, node: &'ast syn::Path) {
        let parts: Vec<_> = node
            .segments
            .iter()
            .map(|segment| segment.ident.to_string())
            .collect();
        self.inspect(&parts, node.span());
        visit::visit_path(self, node);
    }

    fn visit_attribute(&mut self, node: &'ast syn::Attribute) {
        if let syn::Meta::List(list) = &node.meta {
            self.macro_paths(list.tokens.clone());
        }
        visit::visit_attribute(self, node);
    }

    fn visit_macro(&mut self, node: &'ast syn::Macro) {
        if !matches!(
            self.policy.crate_name.as_str(),
            "weft-cli" | "weft-writfold" | "weft-quality"
        ) && node.path.segments.last().is_some_and(|segment| {
            matches!(
                segment.ident.to_string().as_str(),
                "print"
                    | "println"
                    | "eprint"
                    | "eprintln"
                    | "dbg"
                    | "include"
                    | "include_str"
                    | "include_bytes"
                    | "env"
                    | "option_env"
            )
        }) {
            self.error(
                "WQ404",
                node.span(),
                "IO and environment macros are prohibited here",
            );
        }
        self.macro_paths(node.tokens.clone());
        visit::visit_macro(self, node);
    }
}

fn test_only(attributes: &[syn::Attribute]) -> bool {
    attributes.iter().any(|attribute| {
        attribute.path().is_ident("test")
            || (attribute.path().is_ident("cfg")
                && attribute
                    .parse_args::<syn::Path>()
                    .is_ok_and(|path| path.is_ident("test")))
    })
}

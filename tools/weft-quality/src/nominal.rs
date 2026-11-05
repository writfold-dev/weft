mod boundary;
mod existing;
mod validation;

use crate::{Policy, Report, Severity};
use syn::{
    spanned::Spanned,
    visit::{self, Visit},
};

pub(crate) fn check(policy: &Policy, path: &str, file: &syn::File, report: &mut Report) {
    NominalCheck {
        policy,
        path,
        report,
        nominal_owner: false,
        private_owner: false,
        scope: &file.items,
    }
    .visit_file(file);
}

struct NominalCheck<'a, 'ast> {
    policy: &'a Policy,
    path: &'a str,
    report: &'a mut Report,
    nominal_owner: bool,
    private_owner: bool,
    scope: &'ast [syn::Item],
}

fn exposed(visibility: &syn::Visibility) -> bool {
    !matches!(visibility, syn::Visibility::Inherited)
}

impl NominalCheck<'_, '_> {
    fn error(&mut self, code: &str, span: proc_macro2::Span, message: &str) {
        self.report
            .push(self.path, code, Severity::Error, span, message.into());
    }

    fn fields(&mut self, fields: &syn::Fields) {
        for field in fields {
            if exposed(&field.vis) {
                self.error(
                    "WQ301",
                    field.span(),
                    "nominal representation fields must be private",
                );
            }
        }
    }

    fn derives(&mut self, attributes: &[syn::Attribute]) {
        for attribute in attributes {
            if !attribute.path().is_ident("derive") {
                continue;
            }
            let Ok(paths) = attribute.parse_args_with(
                syn::punctuated::Punctuated::<syn::Path, syn::Token![,]>::parse_terminated,
            ) else {
                continue;
            };
            for path in paths {
                if path.segments.last().is_some_and(|part| {
                    matches!(part.ident.to_string().as_str(), "Default" | "Deserialize")
                }) {
                    self.error(
                        "WQ305",
                        path.span(),
                        "derived construction bypasses nominal validation",
                    );
                }
            }
        }
    }
}

impl<'ast> Visit<'ast> for NominalCheck<'_, 'ast> {
    fn visit_item_struct(&mut self, node: &'ast syn::ItemStruct) {
        if self.nominal(&node.ident.to_string()) {
            self.fields(&node.fields);
            self.derives(&node.attrs);
            if exposed(&node.vis) && node.fields.is_empty() {
                self.error(
                    "WQ301",
                    node.span(),
                    "empty nominal structs expose unchecked construction",
                );
            }
        }
        visit::visit_item_struct(self, node);
    }

    fn visit_item_enum(&mut self, node: &'ast syn::ItemEnum) {
        if self.nominal(&node.ident.to_string()) && exposed(&node.vis) {
            self.error(
                "WQ301",
                node.span(),
                "public nominal enum variants bypass checked construction",
            );
        }
        visit::visit_item_enum(self, node);
    }

    fn visit_item_union(&mut self, node: &'ast syn::ItemUnion) {
        if self.nominal(&node.ident.to_string()) {
            self.error(
                "WQ301",
                node.span(),
                "nominal unions cannot enforce a validated representation",
            );
        }
        visit::visit_item_union(self, node);
    }

    fn visit_item_type(&mut self, node: &'ast syn::ItemType) {
        if self.nominal(&node.ident.to_string()) {
            self.error(
                "WQ302",
                node.span(),
                "nominal identities must not be type aliases",
            );
        }
        visit::visit_item_type(self, node);
    }

    fn visit_item_impl(&mut self, node: &'ast syn::ItemImpl) {
        let private_owner = self.private_owner;
        self.private_owner = boundary::private_owner(&node.self_ty, self.scope);
        let previous = std::mem::replace(&mut self.nominal_owner, false);
        if self.contains_nominal(&node.self_ty) {
            self.nominal_owner = true;
            if let Some((_, path, _)) = &node.trait_ {
                if path.segments.last().is_some_and(|segment| {
                    matches!(
                        segment.ident.to_string().as_str(),
                        "From" | "Default" | "Deserialize"
                    )
                }) {
                    self.error(
                        "WQ305",
                        path.span(),
                        "infallible or unchecked trait construction is prohibited",
                    );
                }
                if path
                    .segments
                    .last()
                    .is_some_and(|segment| segment.ident == "TryFrom")
                {
                    for item in &node.items {
                        if let syn::ImplItem::Fn(function) = item {
                            self.constructor(
                                &syn::Visibility::Public(Default::default()),
                                &function.sig,
                                &function.block,
                            );
                        }
                    }
                }
            }
        }
        visit::visit_item_impl(self, node);
        self.nominal_owner = previous;
        self.private_owner = private_owner;
    }

    fn visit_impl_item_fn(&mut self, node: &'ast syn::ImplItemFn) {
        if !self.private_owner {
            self.constructor(&node.vis, &node.sig, &node.block);
        }
        visit::visit_impl_item_fn(self, node);
    }

    fn visit_item_fn(&mut self, node: &'ast syn::ItemFn) {
        self.constructor(&node.vis, &node.sig, &node.block);
        visit::visit_item_fn(self, node);
    }

    fn visit_item_const(&mut self, node: &'ast syn::ItemConst) {
        if exposed(&node.vis) && self.contains_nominal(&node.ty) {
            self.error(
                "WQ303",
                node.span(),
                "public nominal constants bypass checked construction",
            );
        }
        visit::visit_item_const(self, node);
    }

    fn visit_impl_item_const(&mut self, node: &'ast syn::ImplItemConst) {
        if exposed(&node.vis) && self.contains_nominal(&node.ty) {
            self.error(
                "WQ303",
                node.span(),
                "public nominal constants bypass checked construction",
            );
        }
        visit::visit_impl_item_const(self, node);
    }

    fn visit_item_mod(&mut self, node: &'ast syn::ItemMod) {
        let previous = self.scope;
        if let Some((_, items)) = &node.content {
            self.scope = items;
        }
        visit::visit_item_mod(self, node);
        self.scope = previous;
    }
}

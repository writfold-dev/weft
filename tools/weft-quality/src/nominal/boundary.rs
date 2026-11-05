use super::{NominalCheck, existing, validation};
use syn::{spanned::Spanned, visit::Visit};

impl NominalCheck<'_, '_> {
    pub(super) fn nominal(&self, name: &str) -> bool {
        name.ends_with("Id")
            || name.ends_with("ID")
            || name.ends_with("Span")
            || name.ends_with("Digest")
            || name.ends_with("Identity")
            || self.policy.nominal_types.iter().any(|value| value == name)
            || (name == "Self" && self.nominal_owner)
    }

    pub(super) fn contains_nominal(&self, ty: &syn::Type) -> bool {
        match ty {
            syn::Type::Reference(reference) => self.contains_nominal(&reference.elem),
            syn::Type::Tuple(tuple) => tuple.elems.iter().any(|ty| self.contains_nominal(ty)),
            syn::Type::Path(path) => path.path.segments.iter().any(|segment| {
                self.nominal(&segment.ident.to_string()) || match &segment.arguments {
                    syn::PathArguments::AngleBracketed(arguments) => arguments.args.iter().any(|arg| {
                        matches!(arg, syn::GenericArgument::Type(ty) if self.contains_nominal(ty))
                    }),
                    _ => false,
                }
            }),
            _ => false,
        }
    }

    pub(super) fn constructor(
        &mut self,
        visibility: &syn::Visibility,
        signature: &syn::Signature,
        body: &syn::Block,
    ) {
        if !matches!(visibility, syn::Visibility::Public(_)) {
            return;
        }
        let syn::ReturnType::Type(_, ty) = &signature.output else {
            return;
        };
        if !self.contains_nominal(ty) {
            return;
        }
        let mut construction = Construction {
            check: self,
            found: false,
        };
        construction.visit_block(body);
        if !construction.found && existing::returned(signature, body) {
            return;
        }
        let result = matches!(ty.as_ref(), syn::Type::Path(path)
            if path.path.segments.last().is_some_and(|segment| segment.ident == "Result"));
        if !result {
            self.error(
                "WQ303",
                signature.span(),
                "public nominal construction must return Result",
            );
        } else if !validation::fallible(body) {
            self.error(
                "WQ304",
                signature.span(),
                "nominal constructor needs fallible validation (? or an Err branch) or direct Result delegation",
            );
        }
    }
}

// Only declarations in the current lexical module establish private owners.
// An out-of-file owner is unknown, not presumed private; re-exports and type
// resolution require compiler-backed review rather than this syntactic pass.
pub(super) fn private_owner(ty: &syn::Type, items: &[syn::Item]) -> bool {
    let syn::Type::Path(path) = ty else {
        return false;
    };
    if path.qself.is_some() || path.path.segments.len() != 1 {
        return false;
    }
    let Some(segment) = path.path.segments.last() else {
        return false;
    };
    items.iter().any(|item| {
        let (name, visibility) = match item {
            syn::Item::Struct(item) => (&item.ident, &item.vis),
            syn::Item::Enum(item) => (&item.ident, &item.vis),
            syn::Item::Union(item) => (&item.ident, &item.vis),
            _ => return false,
        };
        *name == segment.ident && !matches!(visibility, syn::Visibility::Public(_))
    })
}

struct Construction<'a, 'b, 'ast> {
    check: &'a NominalCheck<'b, 'ast>,
    found: bool,
}

impl<'ast> Visit<'ast> for Construction<'_, '_, '_> {
    fn visit_expr_call(&mut self, node: &'ast syn::ExprCall) {
        if let syn::Expr::Path(path) = node.func.as_ref() {
            self.found |= path
                .path
                .segments
                .iter()
                .any(|segment| self.check.nominal(&segment.ident.to_string()));
        }
        syn::visit::visit_expr_call(self, node);
    }

    fn visit_expr_struct(&mut self, node: &'ast syn::ExprStruct) {
        self.found |= node
            .path
            .segments
            .iter()
            .any(|segment| self.check.nominal(&segment.ident.to_string()));
        syn::visit::visit_expr_struct(self, node);
    }
}

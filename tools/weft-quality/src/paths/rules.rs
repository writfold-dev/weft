use super::PathCheck;
use crate::dependencies::{allowed_internal, development_addition};
use proc_macro2::Span;
use std::{borrow::Cow, collections::BTreeSet};

impl PathCheck<'_> {
    pub(super) fn inspect_macro(&mut self, parts: &[String], span: Span, call: bool) {
        let alias = parts
            .first()
            .is_some_and(|name| self.aliases.contains_key(name));
        if parts.len() > 1 || alias || call {
            self.inspect(parts, span);
        }
    }

    pub(super) fn inspect(&mut self, parts: &[String], span: Span) {
        let Some(first) = parts.first() else {
            return;
        };
        let mut resolved = Cow::Borrowed(parts);
        let mut visited = BTreeSet::new();
        while let Some(prefix) = resolved.first().and_then(|name| self.aliases.get(name)) {
            if !visited.insert(resolved[0].clone()) {
                break;
            }
            let mut next = prefix.clone();
            next.extend_from_slice(&resolved[1..]);
            resolved = Cow::Owned(next);
        }
        let root = resolved.first().map_or(first.as_str(), String::as_str);
        self.value_rules(&resolved, span);
        self.io_rules(root, &resolved, span);
        self.dependency_rule(root, span);
    }

    fn value_rules(&mut self, resolved: &[String], span: Span) {
        if resolved
            .iter()
            .any(|part| matches!(part.as_str(), "panic" | "panic_any" | "resume_unwind"))
        {
            self.error("WQ202", span, "panic paths and aliases are prohibited");
        }
        if self.policy.is_core()
            && resolved.iter().any(|part| {
                matches!(
                    part.as_str(),
                    "serde" | "serde_json" | "Serialize" | "Deserialize" | "Any"
                )
            })
        {
            self.error(
                "WQ403",
                span,
                "serde, generic JSON and Any are prohibited in the semantic core",
            );
        }
        if !matches!(
            self.policy.crate_name.as_str(),
            "weft-wire" | "weft-quality"
        ) && !(self.test_context && self.policy.crate_name == "weft-cli")
            && resolved.iter().any(|part| part == "serde_json")
        {
            self.error("WQ403", span, "generic JSON values belong in weft-wire");
        }
    }

    fn io_rules(&mut self, root: &str, resolved: &[String], span: Span) {
        let allowed = matches!(
            self.policy.crate_name.as_str(),
            "weft-cli" | "weft-writfold" | "weft-quality"
        );
        let standard = root == "std"
            && resolved.get(1).is_some_and(|part| {
                matches!(
                    part.as_str(),
                    "fs" | "io" | "net" | "os" | "process" | "thread" | "time" | "env"
                )
            });
        let external = matches!(
            root,
            "tokio"
                | "async_std"
                | "reqwest"
                | "ureq"
                | "hyper"
                | "socket2"
                | "mio"
                | "libc"
                | "nix"
        );
        if !allowed && (standard || external) {
            self.error(
                "WQ404",
                span,
                "IO, process, network and clock paths are prohibited here",
            );
        }
        if self.policy.crate_name == "weft-writfold"
            && root == "std"
            && resolved
                .get(1)
                .is_some_and(|part| matches!(part.as_str(), "fs" | "net" | "os"))
        {
            self.error(
                "WQ404",
                span,
                "the Writfold client admits shared-stdio process IO, not filesystem/network IO",
            );
        }
    }

    fn dependency_rule(&mut self, root: &str, span: Span) {
        if !root.starts_with("weft_") {
            return;
        }
        let dependency = root.replace('_', "-");
        if dependency != self.policy.crate_name
            && !allowed_internal(&self.policy.crate_name, &dependency)
            && !(self.test_context && development_addition(&self.policy.crate_name, &dependency))
        {
            self.error(
                "WQ401",
                span,
                "source path crosses a forbidden crate dependency direction",
            );
        }
    }
}

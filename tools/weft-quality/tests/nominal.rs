#![forbid(unsafe_code)]

use weft_quality::{Policy, check_source};

#[test]
fn private_fallible_construction_is_admitted() {
    let source = "#![forbid(unsafe_code)]\n\
        pub struct BindingId(u32);\n\
        impl BindingId {\n\
            pub fn try_new(value: u32) -> Result<Self, ()> {\n\
                if value == 0 { return Err(()); }\n\
                Ok(Self(value))\n\
            }\n\
            pub fn value(&self) -> u32 { self.0 }\n\
        }";
    let report = check_source(&Policy::new("weft-domain"), "valid.rs", source, true);
    assert!(!report.failed());
}

#[test]
fn nominal_bypass_forms_are_rejected() {
    for (item, code) in [
        ("pub struct BindingId(pub u32);", "WQ301"),
        ("pub struct SourceSpan { pub(crate) start: usize }", "WQ301"),
        ("pub type QueryDigest = String;", "WQ302"),
        ("pub enum ExternalIdentity { Raw(String) }", "WQ301"),
        ("pub struct TraceId;", "WQ301"),
        ("pub struct TraceId {}", "WQ301"),
        ("union TraceId { raw: u32 }", "WQ301"),
        (
            "struct TraceId(u32); impl TryFrom<u32> for TraceId { type Error = (); fn try_from(x: u32) -> Result<Self, Self::Error> { Ok(Self(x)) } }",
            "WQ304",
        ),
        (
            "pub struct AtomId(u32); impl AtomId { pub fn new(x: u32) -> Self { Self(x) } }",
            "WQ303",
        ),
        (
            "struct AtomId(u32); pub fn make(x: u32) -> AtomId { AtomId(x) }",
            "WQ303",
        ),
        (
            "pub struct AtomId(u32); impl AtomId { pub fn new(x: u32) -> Result<Self, ()> { Ok(Self(x)) } }",
            "WQ304",
        ),
        ("#[derive(Default)] struct AtomId(u32);", "WQ305"),
        (
            "struct AtomId(u32); impl From<u32> for AtomId { fn from(x: u32) -> Self { Self(x) } }",
            "WQ305",
        ),
        (
            "struct AtomId(u32); impl AtomId { pub const ZERO: Self = Self(0); }",
            "WQ303",
        ),
    ] {
        let source = format!("#![forbid(unsafe_code)]\n{item}");
        let report = check_source(&Policy::new("weft-domain"), "invalid.rs", &source, true);
        assert!(
            report.findings.iter().any(|finding| finding.code == code),
            "missing {code}"
        );
    }
}

#[test]
fn nominal_constructor_cannot_hide_fallibility_inside_a_closure() {
    let source = "#![forbid(unsafe_code)]\npub struct CheckId(u32); impl CheckId {\n\
        pub fn new(x: u32) -> Result<Self, ()> { let unused = || { validate()?; Ok(()) }; Ok(Self(x)) } }";
    let report = check_source(&Policy::new("weft-domain"), "closure.rs", source, true);
    assert!(
        report
            .findings
            .iter()
            .any(|finding| finding.code == "WQ304")
    );
}

#[test]
fn explicit_nominal_names_cover_external_identity_domains() {
    let mut policy = Policy::new("weft-domain");
    policy.nominal_types.push("RemoteKey".into());
    let report = check_source(
        &policy,
        "external.rs",
        "#![forbid(unsafe_code)]\npub struct RemoteKey(pub String);",
        true,
    );
    assert!(
        report
            .findings
            .iter()
            .any(|finding| finding.code == "WQ301")
    );
}

#[test]
fn ordinary_value_records_are_not_nominal_ids() {
    let report = check_source(
        &Policy::new("weft-domain"),
        "value.rs",
        "#![forbid(unsafe_code)]\npub struct Value { pub count: u32 }",
        true,
    );
    assert!(!report.failed());
}

#[test]
fn existing_nominal_values_are_not_raw_construction() {
    for item in [
        "pub struct Prepared { query: NodeId } impl Prepared { pub fn query(&self) -> NodeId { self.query } }",
        "pub struct Prepared { query: NodeId } impl Prepared { pub fn query(&self) -> &NodeId { &self.query } }",
        "pub struct Declarations { names: std::collections::BTreeMap<String, NodeId> } impl Declarations { pub fn find(&self, name: &str) -> Option<NodeId> { self.names.get(name).copied() } }",
        "pub enum Value { Natural(u32, NodeId), Other { span: NodeId } } impl Value { pub fn span(&self) -> NodeId { match self { Self::Natural(_, span) => *span, Self::Other { span } => *span } } }",
        "pub fn identity(value: NodeId) -> NodeId { value }",
        "pub fn identity(value: NodeId) -> Result<NodeId, ()> { Ok(value) }",
        "pub fn identity(value: NodeId) -> Option<NodeId> { Some(value) }",
        "pub struct Prepared { query: NodeId } impl Prepared { pub fn query(&self) -> NodeId { return self.query; } }",
    ] {
        let source = format!("#![forbid(unsafe_code)]\npub struct NodeId(u32);\n{item}");
        let report = check_source(&Policy::new("weft-domain"), "getter.rs", &source, true);
        assert!(!report.failed(), "getter rejected: {item}");
    }
}

#[test]
fn crate_private_factories_and_source_arenas_are_not_public_boundaries() {
    for item in [
        "pub struct NodeId(u32); impl NodeId { pub(crate) fn at(raw: u32) -> Self { Self(raw) } }",
        "pub struct NodeId(u32); impl NodeId { fn at(raw: u32) -> Self { Self(raw) } }",
        "pub(crate) struct NodeId(u32); impl NodeId { pub fn at(raw: u32) -> Self { Self(raw) } }",
        "struct NodeId(u32); struct Arena; impl Arena { pub fn push(&mut self, raw: u32) -> NodeId { NodeId(raw) } }",
        "pub(crate) struct NodeId(u32); pub(crate) struct Arena; impl Arena { pub fn push(&mut self, raw: u32) -> NodeId { NodeId(raw) } }",
        "pub struct NodeId(u32); pub(crate) fn at(raw: u32) -> NodeId { NodeId(raw) }",
    ] {
        let source = format!("#![forbid(unsafe_code)]\n{item}");
        let report = check_source(&Policy::new("weft-domain"), "private.rs", &source, true);
        assert!(!report.failed(), "private factory rejected: {item}");
    }
}

#[test]
fn direct_fallible_delegation_is_validation_shape() {
    for body in [
        "Self::checked(raw)",
        "return Self::checked(raw);",
        "Self::checked(raw).map_err(|error| error)",
        "{ Self::checked(raw) }",
    ] {
        let source = format!(
            "#![forbid(unsafe_code)]\npub struct NodeId(u32); impl NodeId {{
                fn checked(raw: u32) -> Result<Self, ()> {{
                    if raw == 0 {{ return Err(()); }} Ok(Self(raw))
                }}
                pub fn cover(raw: u32) -> Result<Self, ()> {{ {body} }}
            }}"
        );
        let report = check_source(&Policy::new("weft-domain"), "delegate.rs", &source, true);
        assert!(!report.failed(), "delegation rejected: {body}");
    }
}

#[test]
fn getters_and_delegation_do_not_admit_raw_public_construction() {
    for (item, code) in [
        (
            "pub struct Arena; impl Arena { pub fn push(&mut self, raw: u32) -> NodeId { NodeId(raw) } }",
            "WQ303",
        ),
        (
            "impl NodeId { pub fn replace(&self, raw: u32) -> Self { Self(raw) } }",
            "WQ303",
        ),
        (
            "pub fn make(raw: u32) -> Option<NodeId> { Some(NodeId(raw)) }",
            "WQ303",
        ),
        ("pub fn make(raw: u32) -> NodeId { hidden(raw) }", "WQ303"),
        (
            "use NodeId as Alias; pub fn make(raw: u32) -> NodeId { Alias(raw) }",
            "WQ303",
        ),
        (
            "pub fn make(raw: u32) -> NodeId { let value = hidden(raw); value }",
            "WQ303",
        ),
        (
            "pub fn make(raw: u32) -> NodeId { hidden(raw).id }",
            "WQ303",
        ),
        (
            "pub fn make(raw: u32) -> Result<NodeId, ()> { Ok(NodeId(raw)) }",
            "WQ304",
        ),
        (
            "pub fn make(raw: u32) -> Result<NodeId, ()> { return Ok(NodeId(raw)); }",
            "WQ304",
        ),
        (
            "pub fn make(raw: u32) -> Result<NodeId, ()> { Ok(NodeId(raw)).map_err(|error| error) }",
            "WQ304",
        ),
        (
            "pub fn make(raw: u32) -> Result<NodeId, ()> { Ok(hidden(raw)) }",
            "WQ304",
        ),
        (
            "impl TryFrom<u32> for NodeId { type Error = (); fn try_from(raw: u32) -> Result<Self, ()> { Ok(Self(raw)) } }",
            "WQ304",
        ),
        ("pub const ZERO: NodeId = NodeId(0);", "WQ303"),
    ] {
        let source = format!("#![forbid(unsafe_code)]\npub struct NodeId(u32);\n{item}");
        let report = check_source(&Policy::new("weft-domain"), "raw.rs", &source, true);
        assert!(
            report.findings.iter().any(|finding| finding.code == code),
            "missing {code}: {item}"
        );
    }
}

#[test]
fn private_owner_visibility_does_not_leak_between_modules() {
    let source = "#![forbid(unsafe_code)]
        pub struct NodeId(u32);
        mod internal { struct Arena; }
        pub struct Arena;
        impl Arena { pub fn push(raw: u32) -> NodeId { NodeId(raw) } }";
    let report = check_source(&Policy::new("weft-domain"), "scope.rs", source, true);
    assert!(
        report
            .findings
            .iter()
            .any(|finding| finding.code == "WQ303")
    );
}

#[test]
fn span_cover_can_delegate_validation_of_combined_bounds() {
    let source = "#![forbid(unsafe_code)]
        pub struct SourceSpan { start: usize, end: usize }
        impl SourceSpan {
            pub fn checked(source: &str, start: usize, end: usize) -> Result<Self, ()> {
                if start > end || end > source.len() { return Err(()); }
                Ok(Self { start, end })
            }
            pub fn cover(self, other: Self, source: &str) -> Result<Self, ()> {
                Self::checked(source, self.start.min(other.start), self.end.max(other.end))
            }
        }";
    let report = check_source(&Policy::new("weft-domain"), "span.rs", source, true);
    assert!(!report.failed());
}

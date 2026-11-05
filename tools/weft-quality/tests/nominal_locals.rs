#![forbid(unsafe_code)]

use weft_quality::{Policy, check_source};

#[test]
fn immutable_lookup_results_can_be_returned_after_diagnostics() {
    let source = r#"#![forbid(unsafe_code)]
#[derive(Clone, Copy)] pub struct ItemId(u32);
struct Names { ids: Vec<ItemId> }
impl Names { fn find(&self, key: usize) -> Option<ItemId> { self.ids.get(key).copied() } }
pub struct Lookup { names: Names, misses: usize }
impl Lookup {
    pub fn find(&mut self, key: usize) -> Option<ItemId> {
        let item = self.names.find(key);
        if item.is_none() { self.misses += 1; }
        item
    }
}
"#;
    let report = check_source(&Policy::new("weft-domain"), "lookup.rs", source, true);
    assert!(!report.failed(), "{:?}", report.findings);
}

#[test]
fn shadowing_and_early_returns_cannot_launder_unknown_construction() {
    for body in [
        "let item = self.item; let item = raw(value); item",
        "let item = self.item; if value == 0 { return raw(value); } item",
        "let mut item = self.item; item = raw(value); item",
    ] {
        let source = format!(
            r#"#![forbid(unsafe_code)]
#[derive(Clone, Copy)] pub struct ItemId(u32);
fn raw(value: u32) -> ItemId {{ ItemId(value) }}
pub struct Lookup {{ item: ItemId }}
impl Lookup {{ pub fn bad(&self, value: u32) -> ItemId {{ {body} }} }}
"#
        );
        let report = check_source(&Policy::new("weft-domain"), "raw.rs", &source, true);
        assert!(
            report
                .findings
                .iter()
                .any(|finding| finding.code == "WQ303"),
            "{body}: {:?}",
            report.findings
        );
    }
}

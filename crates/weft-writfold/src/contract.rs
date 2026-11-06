//! The exact owner-pinned `writfold.agent/1` control-contract identity.
//!
//! These values are consumed unchanged from the owner-landed artifact vendored
//! at `contracts/writfold-agent-1`. Any runtime deviation from them is an
//! identity refusal: the client never negotiates around a changed digest,
//! method set or capability set, and it never treats an ephemeral session
//! label as knowledge authority.

use weft_wire::rpc::InitializeResult;

/// SHA-256 of the pinned `contract.json` inside the owner archive. The server
/// returns this digest on initialization; both sides must agree exactly.
pub const CONTRACT_SHA256: &str =
    "b673d10f7c14c73d8f5778cfb9b2e84a98a159f1553d5c008054402ee85e7be2";
/// Methods this profile implements; requesting anything else is refused.
pub const METHODS: [&str; 2] = ["initialize", "shutdown"];
/// Capabilities the owner advertised; the client may request no others.
pub const CAPABILITIES: [&str; 1] = ["notifications"];

/// A validated admission of one live control session.
///
/// Constructed only through [`Admission::checked`], which refuses any
/// deviation from the pinned artifact identity. Session labels are ephemeral
/// transport-process identifiers: they name no realm, corpus or grant.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Admission {
    initialize: InitializeResult,
}
impl Admission {
    pub fn checked(initialize: InitializeResult) -> Result<Self, String> {
        if &*initialize.contract_sha256 != CONTRACT_SHA256 {
            return Err(format!(
                "contract digest {} does not match the pinned artifact {}",
                initialize.contract_sha256, CONTRACT_SHA256
            ));
        }
        if &*initialize.contract_namespace != "writfold-agent-contract"
            || initialize.contract_schema != 1
        {
            return Err("contract namespace/schema is not the pinned artifact".into());
        }
        if initialize.methods.len() != METHODS.len()
            || initialize
                .methods
                .iter()
                .any(|method| !METHODS.contains(&&**method))
        {
            return Err("server advertises methods outside the pinned control set".into());
        }
        if initialize
            .capabilities
            .iter()
            .any(|capability| !CAPABILITIES.contains(&&**capability))
        {
            return Err("server advertises capabilities outside the pinned control set".into());
        }
        if initialize.generation == 0 {
            return Err("first admitted envelope must consume generation 1".into());
        }
        if initialize.session.instance.is_empty() || initialize.session.incarnation.is_empty() {
            return Err("session labels are absent".into());
        }
        Ok(Self { initialize })
    }
    pub fn session(&self) -> &weft_wire::rpc::SessionLabels {
        &self.initialize.session
    }
    pub fn generation(&self) -> u64 {
        self.initialize.generation
    }
    pub fn server_version(&self) -> &str {
        &self.initialize.server_version
    }
    pub fn contract_sha256(&self) -> &str {
        &self.initialize.contract_sha256
    }
}
/// Local capability admission: refuse before any bytes are written when the
/// requested spelling is not part of the pinned advertised set.
pub fn admitted_capability(name: &str) -> bool {
    CAPABILITIES.contains(&name)
}

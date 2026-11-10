//! Client-side negative controls at the pure boundaries: no peer process is
//! involved, and no Writfold service is simulated. These exercise what the
//! client must refuse before or while interpreting real peer bytes.

use crate::contract::{Admission, CONTRACT_SHA256, admitted_capability};
use weft_wire::rpc::{
    Bounds, Correlation, Failure, FrameError, InitializeResult, ParseError, Reply, ShutdownResult,
};

type TestResult = Result<(), String>;
const PINNED: &str = "bfa436bac90a97a38b5b70d8a20713cfbd38a12ce35283637d5ac9fa235f3f4a";
/// The first `writfold.trial/1` contract this client pinned before the revision.
const EARLIER: &str = "0baf69b21f1051ee620ca89ba4ec659605c0cf3ddc4ae82a7a9ad8eaf1d9ac3f";
fn initialize_reply(digest: &str, generation: &str) -> String {
    format!(
        "{{\"jsonrpc\":\"2.0\",\"id\":\"r1\",\"result\":{{\
\"protocol_version\":\"2\",\"profile\":\"writfold.agent/1\",\
\"implementation_scope\":\"transport-control-only\",\
\"server\":{{\"name\":\"writfold\",\"version\":\"0\"}},\
\"session\":{{\"instance_id\":\"i1\",\"incarnation\":\"c1\"}},\
\"generation\":{generation},\"capabilities\":[\"notifications\"],\"batch\":false,\
\"notifications\":true,\"max_request_bytes\":65536,\"max_response_bytes\":65536,\
\"methods\":{{\"initialize\":{{}},\"shutdown\":{{}}}},\
\"contract\":{{\"namespace\":\"writfold-agent-contract\",\"schema\":1,\"sha256\":\"{digest}\"}},\
\"trust_boundary\":\"Transport/session control only; no authorized corpus, retained release, grounding or effect service is available.\"}}}}"
    )
}
fn shutdown_reply(generation: &str, instance: &str) -> String {
    format!(
        "{{\"jsonrpc\":\"2.0\",\"id\":\"r2\",\"result\":{{\"exit_code\":0,\"complete\":true,\
\"generation\":{generation},\"session\":{{\"instance_id\":\"{instance}\",\"incarnation\":\"c1\"}},\
\"payload\":{{\"shutdown\":true}}}}}}"
    )
}
fn initialize_converted(digest: &str, generation: &str) -> Result<InitializeResult, String> {
    let reply = Reply::parse(initialize_reply(digest, generation).as_bytes())
        .map_err(|error| format!("fixture reply does not parse: {error}"))?;
    InitializeResult::checked(&reply).map_err(|error| format!("fixture does not convert: {error}"))
}

#[test]
fn pinned_initialize_reply_is_admitted() -> TestResult {
    let admission = Admission::checked(initialize_converted(PINNED, "1")?)?;
    if admission.generation() != 1 {
        return Err("first admitted envelope must carry generation 1".into());
    }
    if admission.contract_sha256() != CONTRACT_SHA256 {
        return Err("admission lost the pinned contract digest".into());
    }
    if &*admission.session().instance != "i1" {
        return Err("admission lost the session instance label".into());
    }
    Ok(())
}
#[test]
fn unpinned_contract_digest_is_refused() -> TestResult {
    let other = format!("{:0>64}", "1");
    if other == PINNED {
        return Err("fixture digest accidentally equals the pin".into());
    }
    match Admission::checked(initialize_converted(&other, "1")?) {
        Ok(_) => Err("an unpinned contract digest was admitted".into()),
        Err(_) => Ok(()),
    }
}
#[test]
fn a_server_for_the_earlier_contract_is_refused() -> TestResult {
    // A binary built before the writfold.trial/1 revision presents the earlier digest; the
    // pin is exact, never a compatibility range, so it must not be admitted.
    match Admission::checked(initialize_converted(EARLIER, "1")?) {
        Ok(_) => Err("a server presenting the earlier contract digest was admitted".into()),
        Err(error) if error.contains(EARLIER) && error.contains(CONTRACT_SHA256) => Ok(()),
        Err(error) => Err(format!("refused for the wrong reason: {error}")),
    }
}
#[test]
fn zero_first_generation_is_refused() -> TestResult {
    match Admission::checked(initialize_converted(PINNED, "0")?) {
        Ok(_) => Err("generation 0 was admitted as a first envelope".into()),
        Err(_) => Ok(()),
    }
}
#[test]
fn unknown_initialize_field_is_refused() -> TestResult {
    let frame = initialize_reply(PINNED, "1")
        .replace("\"trust_boundary\"", "\"extra\":1,\"trust_boundary\"");
    let reply = Reply::parse(frame.as_bytes()).map_err(|error| error.to_string())?;
    match InitializeResult::checked(&reply) {
        Ok(_) => Err("an unknown field was accepted".into()),
        Err(_) => Ok(()),
    }
}
#[test]
fn shutdown_reply_binds_its_session_labels() -> TestResult {
    let reply = Reply::parse(shutdown_reply("2", "i1").as_bytes()).map_err(|e| e.to_string())?;
    let converted = ShutdownResult::checked(&reply).map_err(|e| e.to_string())?;
    if converted.generation != 2 || &*converted.session().instance != "i1" {
        return Err("shutdown conversion lost generation or labels".into());
    }
    Ok(())
}
#[test]
fn capability_admission_is_local() -> TestResult {
    if !admitted_capability("notifications") {
        return Err("the advertised capability must be admitted".into());
    }
    for refused in ["knowledge", "citations", ""] {
        if admitted_capability(refused) {
            return Err(format!("capability {refused:?} must be refused locally"));
        }
    }
    Ok(())
}
#[test]
fn foreign_correlation_is_preserved_not_rewritten() -> TestResult {
    let frame =
        b"{\"jsonrpc\":\"2.0\",\"id\":\"other\",\"error\":{\"code\":-32601,\"message\":\"m\"}}";
    match Reply::parse(frame).map_err(|error| error.to_string())? {
        Reply::Failure {
            correlation,
            failure,
        } => {
            if correlation != Correlation::Text("other".into()) || failure.code != -32601 {
                return Err("foreign correlation or code was rewritten".into());
            }
            Ok(())
        }
        Reply::Result { .. } => Err("error reply parsed as a result".into()),
    }
}
#[test]
fn duplicate_keys_are_refused() -> TestResult {
    let frame = b"{\"jsonrpc\":\"2.0\",\"id\":1,\"id\":2,\"result\":{}}";
    if Reply::parse(frame) != Err(FrameError::Parse(ParseError::DuplicateKey)) {
        return Err("duplicate keys were not refused".into());
    }
    Ok(())
}
#[test]
fn fraction_correlation_tokens_are_refused() -> TestResult {
    let frame = b"{\"jsonrpc\":\"2.0\",\"id\":1.0,\"result\":{}}";
    if Reply::parse(frame)
        != Err(FrameError::Shape(
            "correlation is neither string, integer nor null",
        ))
    {
        return Err("a fraction correlation token was accepted".into());
    }
    Ok(())
}
#[test]
fn result_and_error_together_are_refused() -> TestResult {
    let frame = b"{\"jsonrpc\":\"2.0\",\"id\":\"x\",\"result\":{},\
\"error\":{\"code\":-32600,\"message\":\"m\"}}";
    match Reply::parse(frame) {
        Err(FrameError::Shape(_)) => Ok(()),
        other => Err(format!("result and error together yielded {other:?}")),
    }
}
#[test]
fn failure_replies_keep_their_typed_category() -> TestResult {
    let frame = b"{\"jsonrpc\":\"2.0\",\"id\":1,\"error\":{\"code\":-32000,\"message\":\"no\",\
\"data\":{\"schema_version\":1,\"category\":\"malformed\",\"message\":\"no\"}}}";
    match Reply::parse(frame).map_err(|error| error.to_string())? {
        Reply::Failure { failure, .. } => {
            let expected = Failure {
                code: -32000,
                message: "no".into(),
                category: Some("malformed".into()),
            };
            if failure != expected {
                return Err("failure category was lost or altered".into());
            }
            Ok(())
        }
        Reply::Result { .. } => Err("error reply parsed as a result".into()),
    }
}
#[test]
fn deep_and_overspent_value_trees_are_refused() -> TestResult {
    let wide = format!(
        "{{\"jsonrpc\":\"2.0\",\"id\":\"x\",\"result\":{}}}",
        "[".repeat(2000)
    );
    if Reply::parse(wide.as_bytes()).is_ok() {
        return Err("unbounded depth was accepted".into());
    }
    let bounds = Bounds {
        depth: 1,
        nodes: 8,
        entries: 8,
    };
    if weft_wire::rpc::parse::parse(b"[[1]]", bounds) != Err(ParseError::Depth) {
        return Err("the depth bound was not enforced".into());
    }
    Ok(())
}

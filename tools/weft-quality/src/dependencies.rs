use crate::{Policy, Report};

pub(crate) const VALUE_LIBRARIES: &[&str] = &[
    "num-bigint",
    "num-integer",
    "num-traits",
    "sha2",
    "thiserror",
];

pub(crate) fn allowed_internal(owner: &str, dependency: &str) -> bool {
    let allowed: &[&str] = match owner {
        // The proved decision core has no dependencies at all.
        "weft-core" => &[],
        "weft-domain" => &["weft-core"],
        "weft-frontend" => &["weft-domain"],
        "weft-kernel" | "weft-wire" => &["weft-core", "weft-domain"],
        "weft-writfold" => &["weft-domain", "weft-wire"],
        "weft-cli" => &[
            "weft-domain",
            "weft-frontend",
            "weft-kernel",
            "weft-wire",
            "weft-writfold",
        ],
        "weft-quality" => &[],
        _ => &[],
    };
    allowed.contains(&dependency)
}

pub(crate) fn known_crate(name: &str) -> bool {
    matches!(
        name,
        "weft-core"
            | "weft-domain"
            | "weft-frontend"
            | "weft-kernel"
            | "weft-wire"
            | "weft-writfold"
            | "weft-cli"
            | "weft-quality"
    )
}

fn allowed_external(policy: &Policy, dependency: &str) -> bool {
    match policy.crate_name.as_str() {
        "weft-domain" => VALUE_LIBRARIES.contains(&dependency),
        "weft-cli" => dependency == "sha2",
        "weft-wire" => matches!(dependency, "serde" | "serde_json"),
        "weft-quality" => matches!(dependency, "syn" | "proc-macro2" | "serde" | "serde_json"),
        _ => false,
    }
}
pub(crate) fn development_addition(owner: &str, dependency: &str) -> bool {
    matches!(
        (owner, dependency),
        ("weft-wire", "weft-frontend" | "weft-kernel" | "sha2") | ("weft-cli", "serde_json")
    )
}

pub(crate) fn check(
    policy: &Policy,
    manifest: &str,
    dependencies: &[String],
    development: bool,
) -> Report {
    let mut report = Report::default();
    if !known_crate(&policy.crate_name) {
        report.manifest_error(
            manifest,
            "WQ400",
            format!("unregistered crate boundary: {}", policy.crate_name),
        );
    }
    for dependency in dependencies {
        let internal = dependency.starts_with("weft-");
        let allowed = (development && development_addition(&policy.crate_name, dependency))
            || if internal {
                allowed_internal(&policy.crate_name, dependency)
            } else {
                allowed_external(policy, dependency)
            };
        if !allowed {
            let code = if internal { "WQ401" } else { "WQ402" };
            report.manifest_error(
                manifest,
                code,
                format!(
                    "{} may not depend on {dependency}; unadmitted contracts fail closed",
                    policy.crate_name
                ),
            );
        }
    }
    report.normalize();
    report
}

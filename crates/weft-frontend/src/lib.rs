#![forbid(unsafe_code)]

mod ast;
mod lexer;
mod lower;
mod lower_expr;
mod lower_quantifier;
mod lower_sets;
mod parser;
mod resolve;
mod semantic;
mod types;
mod typing;

use weft_domain::{Analysis, Compilation, Limits};

/// Analyze local structure and types without acquiring external evidence.
pub fn analyze(source: &str, limits: &Limits) -> Analysis {
    match parser::parse(source, limits) {
        Ok(parsed) => semantic::check(&parsed, limits).analysis,
        Err(diagnostics) => Analysis {
            diagnostics,
            ..Analysis::default()
        },
    }
}

/// Compile the explicitly hypothetical local profile, retaining blocked checks.
pub fn compile(source: &str, limits: &Limits) -> Result<Compilation, Box<Analysis>> {
    let parsed = match parser::parse(source, limits) {
        Ok(parsed) => parsed,
        Err(diagnostics) => {
            return Err(Box::new(Analysis {
                diagnostics,
                ..Analysis::default()
            }));
        }
    };
    let checked = semantic::check(&parsed, limits);
    lower::compile(&parsed, checked, limits)
}

#[cfg(test)]
mod semantic_tests;

#[cfg(test)]
mod type_boundary_tests;

#[cfg(test)]
mod algebra_tests;
#[cfg(test)]
mod example_tests;

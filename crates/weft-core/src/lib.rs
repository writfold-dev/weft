//! Weft's pure decision core: the decisions production calls, written in
//! plain safe Rust shaped for the Charon/Aeneas translation.
//!
//! - [`sets`]: finite set algebra over value identities — normalization
//!   (first-occurrence deduplication), union, intersection, left difference,
//!   membership, inclusive subset with its first counterexample, and
//!   extensional equality.
//! - [`verdict`]: classification of a complete finite trace as entailed,
//!   refuted, undetermined or inconsistent.
//! - [`scope`]: the byte-exact comparison behind `weft reuse`.
//!
//! The `proofs` compose gate translates this crate to Lean 4
//! (`proofs/Extracted/`, committed) and proves theorems over that translation
//! (`proofs/Kernel/`). The proofs are about this code: there is no
//! hand-written Lean copy of these functions.
//!
//! Translation rules (each is a requirement of the pinned Charon/Aeneas
//! pipeline or keeps the Lean side first-order and axiom-free):
//!
//! 1. No `#[derive]` and no trait impls in the decision modules. Charon
//!    translates every impl in a module it starts from; derived `Debug`
//!    reaches `core::fmt`, which Aeneas models only as an axiom. The impls
//!    live in `convenience.rs`, outside `[package.metadata.charon] start_from`.
//! 2. Equality that a theorem depends on is an explicit kernel function
//!    (`same_bytes`, scalar `==` on `usize`), never a derived trait.
//! 3. Owned data only, no nested borrows: comparisons own their bytes
//!    (`Vec<u8>`), never `&[&[u8]]`/`&str`. Values are `usize` identities.
//! 4. No `as` casts and no iterator adaptors: indexed `while` loops, which
//!    Aeneas translates to its `loop` combinator.
//! 5. No local named like its module (Aeneas otherwise emits a projection
//!    that Lean misparses).
//! 6. Slices of owned vectors by deref coercion (`&vec`), never
//!    `Vec::as_slice`, which the pinned Aeneas library leaves as an axiom.
#![no_std]
#![forbid(unsafe_code)]

extern crate alloc;

pub mod convenience;
pub mod scope;
pub mod sets;
pub mod verdict;

pub use verdict::{LogicalVerdict, RowRole, TraceRow};

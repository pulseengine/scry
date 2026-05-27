//! FEAT-012 — Verus proof module for scry's wasm-lattice domain.
//!
//! This is a Verus-only crate (built via rules_verus' `verus_library`
//! rule); it is not compiled by Cargo or by rules_rust. Its sole
//! purpose is to provide a stable crate root so future proof files
//! can be added alongside `join_proofs.rs` without churning the
//! BUILD target.

pub mod join_proofs;

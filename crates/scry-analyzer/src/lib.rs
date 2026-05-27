//! scry-analyzer — the v0.1 scry analyzer as a Wasm component.
//!
//! v0.1 scaffold. Implements the `analyzer.analyze` function defined
//! in `wit/scry.wit` (derived from `spar/scry.aadl` per DD-010). The
//! cross-component import of `pulseengine:wasm-lattice/domain` is
//! exercised here to validate the WAC composition path before any
//! real analysis code lands.
//!
//! The real interval-domain fixpoint over a parsed Wasm module — the
//! work that turns FEAT-001 acceptance criterion 1 green —
//! arrives in a follow-on PR. This scaffold returns an empty
//! invariant bundle for any input plus a placeholder diagnostic
//! identifying itself as the v0.1 scaffold.

#![no_std]
extern crate alloc;

use alloc::format;
use alloc::string::ToString;
use alloc::vec;
use alloc::vec::Vec;

use scry_analyzer_component_bindings::exports::pulseengine::scry::analyzer::{
    AbstractValue, AnalysisConfig, AnalysisResult, AnalyzeError, Diagnostic, DiagnosticSeverity,
    Guest, InvariantBundle, LocalInvariant, ProgramPoint,
};
use scry_analyzer_component_bindings::pulseengine::wasm_lattice::domain;

struct Component;

const SCRY_VERSION: &str = "0.1.0-scaffold";
const INVARIANT_SCHEMA_URL: &str = "https://pulseengine.eu/scry-invariants/v1";

impl Guest for Component {
    fn analyze(
        module_bytes: Vec<u8>,
        _config: AnalysisConfig,
    ) -> Result<AnalysisResult, AnalyzeError> {
        // v0.1 scaffold rejects empty input as a smoke-test for the
        // error path. Any non-empty input returns an empty bundle
        // plus a single info diagnostic naming the scaffold version.
        if module_bytes.is_empty() {
            return Err(AnalyzeError::InvalidModule(
                "module bytes are empty".to_string(),
            ));
        }

        // Exercise the cross-component import so the WAC composition
        // path is verified end-to-end at runtime, not just at build
        // time. This is the v0.1 dogfood gate: if the composed
        // component runs and the lattice call returns the expected
        // singleton, the cross-component import works.
        let probe = domain::constant_i32(42);
        let lattice_alive = probe.lo == 42 && probe.hi == 42;

        let invariants = InvariantBundle {
            schema: INVARIANT_SCHEMA_URL.to_string(),
            // Real SHA-256 hashing lands with the wasmparser
            // integration. The scaffold reports the byte length as a
            // visible placeholder.
            module_sha256: format!("scaffold-len-{}", module_bytes.len()),
            // Single hardcoded point exercising the AbstractValue
            // shape end-to-end through the WIT round-trip.
            points: vec![ProgramPoint {
                func_index: 0,
                pc: 0,
                locals: vec![LocalInvariant {
                    local_index: 0,
                    value: AbstractValue::I32Interval(probe),
                }],
            }],
        };

        let diagnostics = vec![Diagnostic {
            severity: DiagnosticSeverity::Info,
            func_index: 0,
            pc: 0,
            message: format!(
                "scry {} scaffold — real fixpoint not yet implemented; lattice cross-component import {}",
                SCRY_VERSION,
                if lattice_alive { "alive" } else { "BROKEN" },
            ),
        }];

        Ok(AnalysisResult {
            invariants,
            diagnostics,
        })
    }
}

scry_analyzer_component_bindings::export!(Component with_types_in scry_analyzer_component_bindings);

//! scry-provenance — the typed boundary between meld and scry for the
//! Wasm Component Model analysis (DD-002, [[FEAT-002]]).
//!
//! ## What this is
//!
//! Per DD-002 (closed 2026-05-26 in favour of option (b)), scry runs its
//! Component-Model analysis on the *original component sources* upstream
//! of meld, while meld emits a minimal `component-provenance` custom
//! section into the fused Core Wasm module. That section maps each
//! fused-module function index back to the component + function it came
//! from. scry's post-meld stage decodes the section and *projects* its
//! Component-Model invariants onto concrete fused-module locations so
//! they stay consumable by loom, witness, and the sigil/rivet evidence
//! chain.
//!
//! This crate is exactly that typed contract: the on-the-wire byte
//! format of the section, plus the projection lookup. meld is the
//! producer (its emitter is a separate cross-repo concern, mirroring
//! FEAT-008 / meld#192); scry is the consumer. Putting the format in
//! one pure crate means both sides agree on the bytes by construction
//! rather than by prose.
//!
//! ## v0.7.0 scope (provenance-first slice)
//!
//! This is the *provenance half* of FEAT-002. It delivers the typed
//! boundary + the projection primitive; the handle-state lattice
//! (fresh/owned/borrowed/dropped) and use-after-drop detection are a
//! later slice. Per DD-002's chosen variant (b.1), the section is the
//! minimal function-origin map only — resource type names and handle
//! shapes are NOT recorded here (scry derives those from the original
//! component sources directly).
//!
//! ## Why a separate, zero-dependency crate
//!
//! The same source compiles into the `wasm32-wasip2` scry-analyzer
//! component (`#![no_std]` + `alloc`) *and* natively into the
//! scry-host-tests harness. Keeping it dependency-free means the
//! encode -> decode -> project round-trip is mechanically falsifiable on
//! the native cargo path (`cargo test`) even while the live component
//! `analyze()` round-trip stays blocked by the wac-compose / wasmtime-45
//! limitation documented in `crates/scry-host-tests/tests/soundness.rs`.
//!
//! ## Binary format (`SCPV` v1)
//!
//! The custom section's *payload* (i.e. the bytes after the Wasm
//! custom-section name `component-provenance`) is:
//!
//! ```text
//! offset  size  field
//! 0       4     magic = b"SCPV" (0x53 0x43 0x50 0x56)
//! 4       1     format-version = 1
//! 5       4     entry-count : u32 little-endian
//! 9       12*n  entries, each:
//!                 0  4  fused-func-index : u32 LE
//!                 4  4  component-id     : u32 LE
//!                 8  4  orig-func-index  : u32 LE
//! ```
//!
//! All multi-byte integers are little-endian. The decoder is strict:
//! it rejects a bad magic, an unknown version, a truncated buffer, and
//! any trailing bytes past the declared entry count — so a malformed or
//! version-mismatched section is a hard error, never a silent
//! partial-parse.

#![cfg_attr(not(test), no_std)]

extern crate alloc;

use alloc::vec::Vec;
use core::fmt;

/// Wasm custom-section name meld writes and scry reads. This is the
/// `name` field of the Wasm custom section, not the payload.
pub const SECTION_NAME: &str = "component-provenance";

/// Payload magic: `b"SCPV"` — "scry component provenance".
pub const MAGIC: [u8; 4] = *b"SCPV";

/// The format version this crate emits and is the maximum it accepts.
pub const FORMAT_VERSION: u8 = 1;

/// Fixed payload header size: 4 (magic) + 1 (version) + 4 (count).
const HEADER_LEN: usize = 9;

/// Fixed per-entry size: three u32s.
const ENTRY_LEN: usize = 12;

/// One fused-module function's origin: which component + which function
/// in that component it was lowered from. This is the minimal
/// function-origin map of DD-002 variant (b.1) — no resource/handle
/// shapes are recorded.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ComponentOrigin {
    /// Index of the function in the fused Core Wasm module meld emitted.
    /// This is the key scry's invariants / call-edges are already
    /// keyed by, so projection is a join on this field.
    pub fused_func_index: u32,
    /// Opaque identifier of the originating component in the
    /// composition graph. Only equality is meaningful; the mapping
    /// from id to a component name (if any) is out of scope for the
    /// minimal section.
    pub component_id: u32,
    /// Index of the function within its originating component, before
    /// fusion.
    pub orig_func_index: u32,
}

/// Why decoding a `component-provenance` payload failed. The decoder is
/// deliberately strict: every failure mode is a distinct, testable
/// variant rather than a lenient best-effort parse.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DecodeError {
    /// The payload is shorter than the fixed 9-byte header.
    TooShortForHeader {
        /// Actual payload length in bytes.
        len: usize,
    },
    /// The first four bytes were not the `SCPV` magic.
    BadMagic {
        /// The four bytes that were found instead.
        found: [u8; 4],
    },
    /// The format-version byte names a version this build cannot decode.
    UnsupportedVersion {
        /// The version byte that was found.
        found: u8,
    },
    /// The declared entry count does not match the number of entry-sized
    /// chunks actually present after the header. Catches both truncation
    /// (fewer bytes than declared) and trailing garbage (more bytes than
    /// declared).
    LengthMismatch {
        /// Entry count declared in the header.
        declared_entries: u32,
        /// Number of payload bytes after the 9-byte header.
        body_len: usize,
    },
}

impl fmt::Display for DecodeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DecodeError::TooShortForHeader { len } => write!(
                f,
                "component-provenance payload too short for header: {len} bytes (need >= {HEADER_LEN})"
            ),
            DecodeError::BadMagic { found } => write!(
                f,
                "component-provenance bad magic: found {found:?}, expected {MAGIC:?}"
            ),
            DecodeError::UnsupportedVersion { found } => write!(
                f,
                "component-provenance unsupported format version {found} (this build accepts <= {FORMAT_VERSION})"
            ),
            DecodeError::LengthMismatch {
                declared_entries,
                body_len,
            } => write!(
                f,
                "component-provenance length mismatch: header declares {declared_entries} entries \
                 ({} body bytes) but {body_len} body bytes are present",
                (*declared_entries as usize).saturating_mul(ENTRY_LEN)
            ),
        }
    }
}

/// Serialize a function-origin table into a `component-provenance`
/// section payload (the bytes after the section name). The output is
/// always a valid `SCPV` v1 payload: `decode(&encode(x)) == Ok(x)`.
pub fn encode(origins: &[ComponentOrigin]) -> Vec<u8> {
    let mut out = Vec::with_capacity(HEADER_LEN + origins.len() * ENTRY_LEN);
    out.extend_from_slice(&MAGIC);
    out.push(FORMAT_VERSION);
    out.extend_from_slice(&(origins.len() as u32).to_le_bytes());
    for o in origins {
        out.extend_from_slice(&o.fused_func_index.to_le_bytes());
        out.extend_from_slice(&o.component_id.to_le_bytes());
        out.extend_from_slice(&o.orig_func_index.to_le_bytes());
    }
    out
}

/// Read a u32 little-endian at `off`. Caller guarantees the slice has at
/// least `off + 4` bytes (the bounds are pre-checked by `decode`).
fn read_u32_le(bytes: &[u8], off: usize) -> u32 {
    u32::from_le_bytes([bytes[off], bytes[off + 1], bytes[off + 2], bytes[off + 3]])
}

/// Decode a `component-provenance` section payload into its
/// function-origin table. Strict: see [`DecodeError`] for every
/// rejected shape. On success the returned vector has exactly the
/// declared number of entries, in file order.
pub fn decode(bytes: &[u8]) -> Result<Vec<ComponentOrigin>, DecodeError> {
    if bytes.len() < HEADER_LEN {
        return Err(DecodeError::TooShortForHeader { len: bytes.len() });
    }
    let magic = [bytes[0], bytes[1], bytes[2], bytes[3]];
    if magic != MAGIC {
        return Err(DecodeError::BadMagic { found: magic });
    }
    let version = bytes[4];
    if version != FORMAT_VERSION {
        return Err(DecodeError::UnsupportedVersion { found: version });
    }
    let declared_entries = read_u32_le(bytes, 5);
    let body_len = bytes.len() - HEADER_LEN;
    // Exact match required: catches truncation AND trailing garbage.
    // Use u64 math so the multiply can't overflow `usize` on a 32-bit
    // host before the comparison.
    let expected_body = (declared_entries as u64).saturating_mul(ENTRY_LEN as u64);
    if expected_body != body_len as u64 {
        return Err(DecodeError::LengthMismatch {
            declared_entries,
            body_len,
        });
    }
    let mut origins = Vec::with_capacity(declared_entries as usize);
    let mut off = HEADER_LEN;
    for _ in 0..declared_entries {
        origins.push(ComponentOrigin {
            fused_func_index: read_u32_le(bytes, off),
            component_id: read_u32_le(bytes, off + 4),
            orig_func_index: read_u32_le(bytes, off + 8),
        });
        off += ENTRY_LEN;
    }
    Ok(origins)
}

/// Project a fused-module function index back to its component origin.
///
/// This is the core of FEAT-002's "associate every Component-Model
/// invariant with a concrete location in the fused module" step: scry's
/// invariants and call-edges are keyed by `fused_func_index`, so
/// attaching an origin is a lookup in the decoded table.
///
/// Returns the first matching origin (meld emits at most one entry per
/// fused function; if a malformed section ever carried duplicates the
/// first wins, which is sound for attribution — it never invents an
/// origin for an unmapped function).
pub fn project(origins: &[ComponentOrigin], fused_func_index: u32) -> Option<ComponentOrigin> {
    origins
        .iter()
        .find(|o| o.fused_func_index == fused_func_index)
        .copied()
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;

    fn sample() -> Vec<ComponentOrigin> {
        vec![
            ComponentOrigin {
                fused_func_index: 0,
                component_id: 0,
                orig_func_index: 0,
            },
            ComponentOrigin {
                fused_func_index: 1,
                component_id: 0,
                orig_func_index: 1,
            },
            ComponentOrigin {
                fused_func_index: 7,
                component_id: 3,
                orig_func_index: 2,
            },
            ComponentOrigin {
                fused_func_index: u32::MAX,
                component_id: u32::MAX,
                orig_func_index: u32::MAX,
            },
        ]
    }

    #[test]
    fn round_trip_is_lossless() {
        let origins = sample();
        let bytes = encode(&origins);
        // Header + 4 entries.
        assert_eq!(bytes.len(), HEADER_LEN + 4 * ENTRY_LEN);
        assert_eq!(&bytes[0..4], &MAGIC);
        assert_eq!(bytes[4], FORMAT_VERSION);
        let decoded = decode(&bytes).expect("round-trip decode");
        assert_eq!(decoded, origins, "decode(encode(x)) must equal x");
    }

    #[test]
    fn empty_table_round_trips() {
        let bytes = encode(&[]);
        assert_eq!(bytes.len(), HEADER_LEN);
        assert_eq!(decode(&bytes), Ok(Vec::new()));
    }

    #[test]
    fn projection_hits_and_misses() {
        let origins = sample();
        assert_eq!(
            project(&origins, 7),
            Some(ComponentOrigin {
                fused_func_index: 7,
                component_id: 3,
                orig_func_index: 2,
            })
        );
        assert_eq!(
            project(&origins, 0),
            Some(ComponentOrigin {
                fused_func_index: 0,
                component_id: 0,
                orig_func_index: 0,
            })
        );
        // An unmapped fused index must not be invented.
        assert_eq!(project(&origins, 2), None);
        assert_eq!(project(&origins, 999), None);
        assert_eq!(project(&[], 0), None);
    }

    #[test]
    fn rejects_short_header() {
        assert_eq!(
            decode(&[0x53, 0x43, 0x50]),
            Err(DecodeError::TooShortForHeader { len: 3 })
        );
        assert_eq!(decode(&[]), Err(DecodeError::TooShortForHeader { len: 0 }));
    }

    #[test]
    fn rejects_bad_magic() {
        let mut bytes = encode(&sample());
        bytes[1] = b'X';
        assert_eq!(
            decode(&bytes),
            Err(DecodeError::BadMagic {
                found: [b'S', b'X', b'P', b'V']
            })
        );
    }

    #[test]
    fn rejects_unsupported_version() {
        let mut bytes = encode(&sample());
        bytes[4] = 2;
        assert_eq!(
            decode(&bytes),
            Err(DecodeError::UnsupportedVersion { found: 2 })
        );
    }

    #[test]
    fn rejects_truncated_body() {
        let mut bytes = encode(&sample());
        // Drop the last 3 bytes of the final entry → body shorter than
        // the header's declared 4 entries.
        bytes.truncate(bytes.len() - 3);
        let body_len = bytes.len() - HEADER_LEN;
        assert_eq!(
            decode(&bytes),
            Err(DecodeError::LengthMismatch {
                declared_entries: 4,
                body_len,
            })
        );
    }

    #[test]
    fn rejects_trailing_garbage() {
        let mut bytes = encode(&sample());
        bytes.push(0xff);
        let body_len = bytes.len() - HEADER_LEN;
        assert_eq!(
            decode(&bytes),
            Err(DecodeError::LengthMismatch {
                declared_entries: 4,
                body_len,
            })
        );
    }

    #[test]
    fn count_overstated_without_bytes_is_rejected() {
        // Header claims 5 entries but no body bytes follow.
        let mut bytes = Vec::new();
        bytes.extend_from_slice(&MAGIC);
        bytes.push(FORMAT_VERSION);
        bytes.extend_from_slice(&5u32.to_le_bytes());
        assert_eq!(
            decode(&bytes),
            Err(DecodeError::LengthMismatch {
                declared_entries: 5,
                body_len: 0,
            })
        );
    }
}

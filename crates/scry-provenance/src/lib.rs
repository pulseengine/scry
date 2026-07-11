//! `scry-provenance` — the `component-provenance` custom-section format
//! (DD-002 / REQ-008): **meld is the producer, scry is the consumer.**
//!
//! This crate is scry's *trusted* decoder for the section meld writes onto a
//! fused Core Wasm module. It is `#![no_std]` and parses a strict little-endian
//! binary format — no JSON parser in the trusted base (scry#63: keep the
//! DO-333 decoder lean; the one-time encoder swap lands on meld, the untrusted
//! std host).
//!
//! ## Binary format (`SCPV` v3)
//!
//! v3 (scry#63 / meld#313) makes scry's binary format the canonical wire shape
//! both sides build to. It adds, over the original v1: the two **fusion
//! premises** meld knows by construction (carried in the fixed header so a
//! consumer reads them without walking entries), a `fused_module_sha256`
//! binding the section to its module, a UTF-8 (length-prefixed) `component_id`
//! (meld's string id), and an optional per-entry `code_range` (the function
//! body's byte span, for DWARF address remapping).
//!
//! ```text
//! offset  size    field
//! 0       4       magic = b"SCPV"
//! 4       1       version = 3              (decoder dispatches AFTER magic)
//! 5       1       bounded_memory : 0|1     premise: no memory.grow in fused core
//! 6       1       closed_world   : 0|1     premise: cross-component imports internalised
//! 7       32      fused_module_sha256      raw bytes, binds section ↔ module
//! 39      4       entry_count : u32 LE
//! 43      …       entries[entry_count], each (variable length):
//!                   0  4        fused_func_index  : u32 LE
//!                   4  4        component_id_len  : u32 LE
//!                   8  len      component_id      : UTF-8 bytes
//!                   …  4        orig_func_index   : u32 LE
//!                   …  1        has_code_range    : 0|1
//!                   [if 1] 4    code_range_start  : u32 LE
//!                          4    code_range_end    : u32 LE
//! ```
//!
//! All multi-byte integers are little-endian. The decoder is strict: it rejects
//! a bad magic, an unknown version, a malformed flag byte, a non-UTF-8
//! component id, a truncated buffer, and any trailing bytes past the declared
//! entries — so a malformed or version-mismatched section is a hard error,
//! never a silent partial-parse. (Premises are *absent* only in older versions;
//! a v3 header always carries them — a consumer reading an older version that
//! lacks the bytes falls back to conservative.)

#![cfg_attr(not(test), no_std)]

extern crate alloc;

use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;

/// Wasm custom-section name meld writes and scry reads. This is the `name`
/// field of the Wasm custom section, not the payload.
pub const SECTION_NAME: &str = "component-provenance";

/// Payload magic: `b"SCPV"` — "scry component provenance".
pub const MAGIC: [u8; 4] = *b"SCPV";

/// The format version this crate emits and is the maximum it accepts.
pub const FORMAT_VERSION: u8 = 3;

/// Fixed header size: 4 (magic) + 1 (version) + 1 (bounded_memory) +
/// 1 (closed_world) + 32 (sha256) + 4 (entry_count).
const HEADER_LEN: usize = 43;

/// The fusion premises meld asserts by construction — facts scry cannot soundly
/// assume on its own but that hold after fusion. Carried in the section header
/// (scry#63). Absent ⇒ a consumer stays conservative; here they are always
/// present in v3.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub struct FusionPremises {
    /// No `memory.grow` in the fused core → linear memory is fixed-size. Lets
    /// the analyzer drop grow-reachability widening.
    pub bounded_memory: bool,
    /// All cross-component imports internalised → no external mutation of fused
    /// state between components. Lets the analyzer tighten reachability.
    pub closed_world: bool,
}

/// The function body's byte span in the fused module (for DWARF address
/// remapping). v2+ per-entry; optional.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CodeRange {
    /// Start byte offset of the function body.
    pub start: u32,
    /// End byte offset (exclusive) of the function body.
    pub end: u32,
}

/// One fused-module function's origin: which component + which function in that
/// component it was lowered from. The minimal function-origin map of DD-002
/// variant (b.1); v3 carries meld's string `component_id` and an optional
/// `code_range`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ComponentOrigin {
    /// Index of the function in the fused Core Wasm module meld emitted — the
    /// key scry's invariants / call-edges are keyed by, so projection is a join
    /// on this field.
    pub fused_func_index: u32,
    /// Identifier of the originating component in the composition graph
    /// (meld's string id; only equality/labelling is meaningful).
    pub component_id: String,
    /// Index of the function within its originating component, before fusion.
    pub orig_func_index: u32,
    /// Byte span of the function body in the fused module, if meld recorded it.
    pub code_range: Option<CodeRange>,
}

/// A fully decoded `component-provenance` section: the fusion premises, the
/// module-binding hash, and the function-origin table.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProvenanceSection {
    /// Fusion premises (header).
    pub premises: FusionPremises,
    /// SHA-256 of the fused module the section was emitted for.
    pub fused_module_sha256: [u8; 32],
    /// Per-function origins, in file order.
    pub origins: Vec<ComponentOrigin>,
}

/// Why decoding a `component-provenance` payload failed. The decoder is
/// deliberately strict: every failure mode is a distinct, testable variant.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DecodeError {
    /// The payload is shorter than the fixed header.
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
    /// A boolean flag byte (a premise, or `has_code_range`) was not 0 or 1.
    MalformedFlag {
        /// Byte offset of the bad flag.
        offset: usize,
        /// The non-boolean value found.
        value: u8,
    },
    /// A `component_id` byte run was not valid UTF-8.
    BadComponentId {
        /// Byte offset where the id started.
        offset: usize,
    },
    /// The payload ended mid-field while decoding an entry.
    Truncated {
        /// Offset at which more bytes were needed.
        offset: usize,
        /// Number of bytes still required there.
        need: usize,
        /// Total payload length.
        len: usize,
    },
    /// Bytes remained after the declared number of entries were decoded.
    TrailingBytes {
        /// Offset where decoding finished.
        at: usize,
        /// Total payload length.
        len: usize,
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
                "component-provenance unsupported format version {found} (this build expects {FORMAT_VERSION})"
            ),
            DecodeError::MalformedFlag { offset, value } => write!(
                f,
                "component-provenance malformed flag byte {value} at offset {offset} (expected 0 or 1)"
            ),
            DecodeError::BadComponentId { offset } => write!(
                f,
                "component-provenance component_id at offset {offset} is not valid UTF-8"
            ),
            DecodeError::Truncated { offset, need, len } => write!(
                f,
                "component-provenance truncated at offset {offset}: need {need} more bytes ({len}-byte payload)"
            ),
            DecodeError::TrailingBytes { at, len } => write!(
                f,
                "component-provenance trailing bytes: decoded through offset {at} of a {len}-byte payload"
            ),
        }
    }
}

/// Serialize a `ProvenanceSection` into a `SCPV` v3 payload (the bytes after the
/// section name). `decode(&encode(x)) == Ok(x)`. (scry's encoder is for tests
/// and tooling; meld is the production producer, building to the same layout.)
pub fn encode(section: &ProvenanceSection) -> Vec<u8> {
    let mut out = Vec::with_capacity(HEADER_LEN + section.origins.len() * 16);
    out.extend_from_slice(&MAGIC);
    out.push(FORMAT_VERSION);
    out.push(section.premises.bounded_memory as u8);
    out.push(section.premises.closed_world as u8);
    out.extend_from_slice(&section.fused_module_sha256);
    out.extend_from_slice(&(section.origins.len() as u32).to_le_bytes());
    for o in &section.origins {
        out.extend_from_slice(&o.fused_func_index.to_le_bytes());
        let id = o.component_id.as_bytes();
        out.extend_from_slice(&(id.len() as u32).to_le_bytes());
        out.extend_from_slice(id);
        out.extend_from_slice(&o.orig_func_index.to_le_bytes());
        match &o.code_range {
            Some(cr) => {
                out.push(1);
                out.extend_from_slice(&cr.start.to_le_bytes());
                out.extend_from_slice(&cr.end.to_le_bytes());
            }
            None => out.push(0),
        }
    }
    out
}

fn take_u32(b: &[u8], off: &mut usize) -> Result<u32, DecodeError> {
    let end = off
        .checked_add(4)
        .filter(|e| *e <= b.len())
        .ok_or(DecodeError::Truncated {
            offset: *off,
            need: 4,
            len: b.len(),
        })?;
    let v = u32::from_le_bytes([b[*off], b[*off + 1], b[*off + 2], b[*off + 3]]);
    *off = end;
    Ok(v)
}

fn take_u8(b: &[u8], off: &mut usize) -> Result<u8, DecodeError> {
    if *off >= b.len() {
        return Err(DecodeError::Truncated {
            offset: *off,
            need: 1,
            len: b.len(),
        });
    }
    let v = b[*off];
    *off += 1;
    Ok(v)
}

fn take_slice<'a>(b: &'a [u8], off: &mut usize, n: usize) -> Result<&'a [u8], DecodeError> {
    let end = off
        .checked_add(n)
        .filter(|e| *e <= b.len())
        .ok_or(DecodeError::Truncated {
            offset: *off,
            need: n,
            len: b.len(),
        })?;
    let s = &b[*off..end];
    *off = end;
    Ok(s)
}

fn decode_flag(byte: u8, offset: usize) -> Result<bool, DecodeError> {
    match byte {
        0 => Ok(false),
        1 => Ok(true),
        value => Err(DecodeError::MalformedFlag { offset, value }),
    }
}

/// Decode a `component-provenance` section payload. Strict: see [`DecodeError`]
/// for every rejected shape. On success the origins are in file order and the
/// whole payload was consumed.
pub fn decode(bytes: &[u8]) -> Result<ProvenanceSection, DecodeError> {
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
    let premises = FusionPremises {
        bounded_memory: decode_flag(bytes[5], 5)?,
        closed_world: decode_flag(bytes[6], 6)?,
    };
    let mut fused_module_sha256 = [0u8; 32];
    fused_module_sha256.copy_from_slice(&bytes[7..39]);

    let mut off = HEADER_LEN;
    let entry_count = {
        let mut h = 39;
        take_u32(bytes, &mut h)? // header count at offset 39 (h advances to 43)
    };
    // Pre-size from the count, but BOUND it by what the remaining payload could
    // possibly hold: `entry_count` is attacker-controlled (up to u32::MAX) from
    // a 43-byte header, and a bare `Vec::with_capacity(entry_count)` panics with
    // "capacity overflow" on a 32-bit target (the wasm32 production build) for a
    // crafted tiny payload — a DoS in the trusted decoder. The smallest possible
    // entry is 13 bytes (fused u32 + id_len u32 + 0-byte id + orig u32 +
    // has_code_range u8), so no more than `body_len / 13` entries can follow;
    // an over-stated count then fails the per-entry `take_*` bound check below.
    let body_len = bytes.len().saturating_sub(HEADER_LEN);
    let cap = (entry_count as usize).min(body_len / 13);
    let mut origins = Vec::with_capacity(cap);
    for _ in 0..entry_count {
        let fused_func_index = take_u32(bytes, &mut off)?;
        let id_len = take_u32(bytes, &mut off)? as usize;
        let id_start = off;
        let id_bytes = take_slice(bytes, &mut off, id_len)?;
        let component_id = match core::str::from_utf8(id_bytes) {
            Ok(s) => String::from(s),
            Err(_) => return Err(DecodeError::BadComponentId { offset: id_start }),
        };
        let orig_func_index = take_u32(bytes, &mut off)?;
        let has_code_range = decode_flag(take_u8(bytes, &mut off)?, off - 1)?;
        let code_range = if has_code_range {
            let start = take_u32(bytes, &mut off)?;
            let end = take_u32(bytes, &mut off)?;
            Some(CodeRange { start, end })
        } else {
            None
        };
        origins.push(ComponentOrigin {
            fused_func_index,
            component_id,
            orig_func_index,
            code_range,
        });
    }
    if off != bytes.len() {
        return Err(DecodeError::TrailingBytes {
            at: off,
            len: bytes.len(),
        });
    }
    Ok(ProvenanceSection {
        premises,
        fused_module_sha256,
        origins,
    })
}

/// Project a fused-module function index back to its component origin. scry's
/// invariants and call-edges are keyed by `fused_func_index`, so attaching an
/// origin is a lookup in the decoded table. Returns the first matching origin;
/// never invents an origin for an unmapped function.
pub fn project(origins: &[ComponentOrigin], fused_func_index: u32) -> Option<ComponentOrigin> {
    origins
        .iter()
        .find(|o| o.fused_func_index == fused_func_index)
        .cloned()
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::string::ToString;
    use alloc::vec;

    fn sample() -> ProvenanceSection {
        ProvenanceSection {
            premises: FusionPremises {
                bounded_memory: true,
                closed_world: false,
            },
            fused_module_sha256: [0xab; 32],
            origins: vec![
                ComponentOrigin {
                    fused_func_index: 0,
                    component_id: "auth".to_string(),
                    orig_func_index: 0,
                    code_range: Some(CodeRange { start: 0, end: 42 }),
                },
                ComponentOrigin {
                    fused_func_index: 1,
                    component_id: "auth".to_string(),
                    orig_func_index: 1,
                    code_range: None,
                },
                ComponentOrigin {
                    fused_func_index: 7,
                    component_id: "db-store".to_string(),
                    orig_func_index: 2,
                    code_range: Some(CodeRange {
                        start: 100,
                        end: u32::MAX,
                    }),
                },
            ],
        }
    }

    #[test]
    fn round_trip_is_lossless() {
        let section = sample();
        let bytes = encode(&section);
        assert_eq!(&bytes[0..4], &MAGIC);
        assert_eq!(bytes[4], FORMAT_VERSION);
        assert_eq!(bytes[5], 1, "bounded_memory");
        assert_eq!(bytes[6], 0, "closed_world");
        let decoded = decode(&bytes).expect("round-trip decode");
        assert_eq!(decoded, section, "decode(encode(x)) must equal x");
    }

    #[test]
    fn premises_in_header_decode_both_ways() {
        for (bm, cw) in [(false, false), (true, false), (false, true), (true, true)] {
            let mut s = sample();
            s.premises = FusionPremises {
                bounded_memory: bm,
                closed_world: cw,
            };
            let d = decode(&encode(&s)).unwrap();
            assert_eq!(d.premises.bounded_memory, bm);
            assert_eq!(d.premises.closed_world, cw);
        }
    }

    #[test]
    fn empty_table_round_trips() {
        let s = ProvenanceSection {
            premises: FusionPremises::default(),
            fused_module_sha256: [0; 32],
            origins: Vec::new(),
        };
        let bytes = encode(&s);
        assert_eq!(bytes.len(), HEADER_LEN);
        assert_eq!(decode(&bytes), Ok(s));
    }

    #[test]
    fn utf8_component_ids_round_trip() {
        let mut s = sample();
        s.origins[0].component_id = "compōnent/ünicode".to_string();
        let d = decode(&encode(&s)).unwrap();
        assert_eq!(d.origins[0].component_id, "compōnent/ünicode");
    }

    #[test]
    fn projection_hits_and_misses() {
        let s = sample();
        assert_eq!(project(&s.origins, 7).unwrap().component_id, "db-store");
        assert_eq!(project(&s.origins, 0).unwrap().orig_func_index, 0);
        assert_eq!(project(&s.origins, 2), None); // unmapped, not invented
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
            Err(DecodeError::BadMagic { found: *b"SXPV" })
        );
    }

    #[test]
    fn rejects_unsupported_version() {
        // A v1/v2 (or future) section is a hard error on this v3 build.
        let mut bytes = encode(&sample());
        bytes[4] = 1;
        assert_eq!(
            decode(&bytes),
            Err(DecodeError::UnsupportedVersion { found: 1 })
        );
    }

    #[test]
    fn rejects_malformed_premise_flag() {
        let mut bytes = encode(&sample());
        bytes[5] = 2; // bounded_memory neither 0 nor 1
        assert_eq!(
            decode(&bytes),
            Err(DecodeError::MalformedFlag {
                offset: 5,
                value: 2
            })
        );
    }

    #[test]
    fn rejects_truncated_entry() {
        let mut bytes = encode(&sample());
        bytes.truncate(bytes.len() - 3); // chop into the last entry
        assert!(matches!(decode(&bytes), Err(DecodeError::Truncated { .. })));
    }

    #[test]
    fn rejects_trailing_bytes() {
        let mut bytes = encode(&sample());
        bytes.push(0xff);
        assert!(matches!(
            decode(&bytes),
            Err(DecodeError::TrailingBytes { .. })
        ));
    }

    #[test]
    fn huge_entry_count_does_not_panic_or_oom() {
        // A 43-byte header declaring u32::MAX entries (no body) must fail with
        // a bounded decode error — never a `Vec::with_capacity` capacity-
        // overflow panic (which aborts on the 32-bit wasm32 production target).
        let mut b = Vec::new();
        b.extend_from_slice(&MAGIC);
        b.push(FORMAT_VERSION);
        b.push(0); // bounded_memory
        b.push(0); // closed_world
        b.extend_from_slice(&[0u8; 32]);
        b.extend_from_slice(&u32::MAX.to_le_bytes()); // entry_count = u32::MAX
        // No entry bytes follow → the first take_u32 of entry 0 is Truncated.
        assert!(matches!(decode(&b), Err(DecodeError::Truncated { .. })));
    }

    #[test]
    fn rejects_bad_utf8_component_id() {
        // Hand-build a one-entry section with an invalid UTF-8 id (0xff).
        let mut b = Vec::new();
        b.extend_from_slice(&MAGIC);
        b.push(FORMAT_VERSION);
        b.push(0); // bounded_memory
        b.push(0); // closed_world
        b.extend_from_slice(&[0u8; 32]);
        b.extend_from_slice(&1u32.to_le_bytes()); // entry_count = 1
        b.extend_from_slice(&0u32.to_le_bytes()); // fused_func_index
        b.extend_from_slice(&1u32.to_le_bytes()); // component_id_len = 1
        b.push(0xff); // invalid UTF-8
        b.extend_from_slice(&0u32.to_le_bytes()); // orig_func_index
        b.push(0); // has_code_range
        assert!(matches!(
            decode(&b),
            Err(DecodeError::BadComponentId { .. })
        ));
    }
}

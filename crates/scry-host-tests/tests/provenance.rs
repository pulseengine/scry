//! Provenance round-trip + projection test — FEAT-002 / FEAT-032 (DD-002).
//!
//! This is the native falsifier for the provenance slice. It exercises the
//! `scry-provenance` crate — the *same source* the `wasm32-wasip2`
//! scry-analyzer component links — directly under `cargo test`, so the
//! meld<->scry section contract is mechanically checked even though a live
//! `analyze()` round-trip is still blocked by the wac-compose / wasmtime-45
//! limitation documented in `tests/soundness.rs`.
//!
//! What it asserts (now against the `SCPV` v3 wire format, scry#63):
//!
//!   * `decode(encode(x)) == x` for a representative section (lossless
//!     round-trip incl. the header premises, sha binding, string component
//!     ids, and optional code ranges).
//!   * `project()` attributes a fused-module function index to its component
//!     origin and never invents an origin for an unmapped index.
//!   * the strict decoder rejects every malformed shape (bad magic, unknown
//!     version, malformed flag, truncation, trailing garbage) rather than
//!     silently partial-parsing.

#![forbid(unsafe_code)]

use scry_provenance::{
    CodeRange, ComponentOrigin, DecodeError, FORMAT_VERSION, FusionPremises, MAGIC,
    ProvenanceSection, SECTION_NAME, decode, encode, project,
};

fn sample() -> ProvenanceSection {
    ProvenanceSection {
        premises: FusionPremises {
            bounded_memory: true,
            closed_world: false,
        },
        fused_module_sha256: [0x5a; 32],
        // Two functions from the lattice component, two from the analyzer,
        // with a non-trivial fused-index gap to prove projection isn't
        // positional, and a mix of present/absent code ranges + a UTF-8 id.
        origins: vec![
            ComponentOrigin {
                fused_func_index: 0,
                component_id: "lattice".to_string(),
                orig_func_index: 0,
                code_range: Some(CodeRange { start: 0, end: 64 }),
            },
            ComponentOrigin {
                fused_func_index: 1,
                component_id: "lattice".to_string(),
                orig_func_index: 1,
                code_range: None,
            },
            ComponentOrigin {
                fused_func_index: 5,
                component_id: "analyzer".to_string(),
                orig_func_index: 0,
                code_range: Some(CodeRange {
                    start: 64,
                    end: 4096,
                }),
            },
            ComponentOrigin {
                fused_func_index: 6,
                component_id: "analyzer".to_string(),
                orig_func_index: 1,
                code_range: None,
            },
        ],
    }
}

#[test]
fn section_name_is_the_meld_contract() {
    // If this string/version ever changes, meld's emitter and scry's reader
    // disagree and projection silently disappears — pin it.
    assert_eq!(SECTION_NAME, "component-provenance");
    assert_eq!(&MAGIC, b"SCPV");
    assert_eq!(FORMAT_VERSION, 3);
}

#[test]
fn round_trip_is_lossless() {
    let section = sample();
    let bytes = encode(&section);
    let decoded = decode(&bytes).expect("round-trip decode must succeed");
    assert_eq!(decoded, section, "decode(encode(x)) must equal x");
}

#[test]
fn premises_survive_the_round_trip() {
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
    assert_eq!(decode(&encode(&s)), Ok(s));
}

#[test]
fn projection_attributes_and_never_invents() {
    let origins = sample().origins;

    let hit = project(&origins, 5).expect("fused func 5 maps");
    assert_eq!(hit.component_id, "analyzer");
    assert_eq!(hit.orig_func_index, 0);

    // Keyed by fused-func-index, not position: index 6 (the 4th entry).
    assert_eq!(project(&origins, 6).unwrap().orig_func_index, 1);

    // Unmapped fused indices must yield None — never a fabricated origin.
    assert_eq!(project(&origins, 2), None);
    assert_eq!(project(&origins, 4), None);
    assert_eq!(project(&origins, 100), None);
    assert_eq!(project(&[], 0), None);
}

#[test]
fn round_trips_through_a_real_wasm_custom_section() {
    // Build a minimal core module and append a real Wasm custom section
    // named `component-provenance` carrying the encoded payload, then confirm
    // it decodes back. This is the exact byte path the analyzer's pre-pass
    // walks: `reader.name() == SECTION_NAME` then `decode(reader.data())`.
    let section = sample();
    let payload = encode(&section);

    let mut module: Vec<u8> = vec![0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00];
    let name = SECTION_NAME.as_bytes();
    let mut body: Vec<u8> = Vec::new();
    write_uleb128(&mut body, name.len() as u64);
    body.extend_from_slice(name);
    body.extend_from_slice(&payload);
    module.push(0x00); // custom section id
    write_uleb128(&mut module, body.len() as u64);
    module.extend_from_slice(&body);

    let mut found: Option<ProvenanceSection> = None;
    for payload in wasmparser::Parser::new(0).parse_all(&module) {
        if let wasmparser::Payload::CustomSection(reader) =
            payload.expect("module the test just built must parse")
            && reader.name() == SECTION_NAME
        {
            found = Some(decode(reader.data()).expect("section payload must decode"));
        }
    }
    assert_eq!(
        found,
        Some(section),
        "the component-provenance custom section must survive Wasm encoding and decode losslessly"
    );
}

#[test]
fn decoder_rejects_malformed_payloads() {
    // Bad magic.
    let mut bad = encode(&sample());
    bad[0] = b'Z';
    assert!(matches!(decode(&bad), Err(DecodeError::BadMagic { .. })));

    // Unknown version (a v1/v2 section is a hard error on this v3 build).
    let mut bad = encode(&sample());
    bad[4] = 1;
    assert_eq!(
        decode(&bad),
        Err(DecodeError::UnsupportedVersion { found: 1 })
    );

    // Malformed premise flag.
    let mut bad = encode(&sample());
    bad[5] = 2;
    assert!(matches!(
        decode(&bad),
        Err(DecodeError::MalformedFlag { .. })
    ));

    // Truncated body (chop into the last entry).
    let mut bad = encode(&sample());
    bad.truncate(bad.len() - 1);
    assert!(matches!(decode(&bad), Err(DecodeError::Truncated { .. })));

    // Trailing garbage.
    let mut bad = encode(&sample());
    bad.push(0x00);
    assert!(matches!(
        decode(&bad),
        Err(DecodeError::TrailingBytes { .. })
    ));

    // Too short for the header.
    assert!(matches!(
        decode(&[0x53, 0x43]),
        Err(DecodeError::TooShortForHeader { .. })
    ));
}

/// Minimal unsigned LEB128 writer — wasmparser reads sizes as LEB128, so the
/// test must encode the custom-section name length and body length the same
/// way. (We don't pull in `wasm-encoder` just for this.)
fn write_uleb128(out: &mut Vec<u8>, mut value: u64) {
    loop {
        let mut byte = (value & 0x7f) as u8;
        value >>= 7;
        if value != 0 {
            byte |= 0x80;
        }
        out.push(byte);
        if value == 0 {
            break;
        }
    }
}

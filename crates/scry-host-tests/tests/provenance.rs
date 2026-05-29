//! Provenance round-trip + projection test — FEAT-002 (DD-002).
//!
//! This is the native falsifier for the v0.7.0 provenance slice. It
//! exercises the `scry-provenance` crate — the *same source* the
//! `wasm32-wasip2` scry-analyzer component links — directly under
//! `cargo test`, so the meld<->scry section contract is mechanically
//! checked even though a live `analyze()` round-trip is still blocked by
//! the wac-compose / wasmtime-45 limitation documented in
//! `tests/soundness.rs`.
//!
//! What it asserts:
//!
//!   * `decode(encode(x)) == x` for representative origin tables
//!     (lossless round-trip — FEAT-002 AC#5, scry half).
//!   * `project()` attributes a fused-module function index to its
//!     component origin and never invents an origin for an unmapped
//!     index (FEAT-002 AC#2, the projection primitive).
//!   * the strict decoder rejects every malformed shape (bad magic,
//!     unknown version, truncation, trailing garbage) rather than
//!     silently partial-parsing.

#![forbid(unsafe_code)]

use scry_provenance::{
    ComponentOrigin, DecodeError, FORMAT_VERSION, MAGIC, SECTION_NAME, decode, encode, project,
};

fn sample() -> Vec<ComponentOrigin> {
    vec![
        // Two functions from component 0 (e.g. the lattice component),
        // one from component 1 (the analyzer), with a non-trivial
        // fused-index gap to prove projection isn't positional.
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
            fused_func_index: 5,
            component_id: 1,
            orig_func_index: 0,
        },
        ComponentOrigin {
            fused_func_index: 6,
            component_id: 1,
            orig_func_index: 1,
        },
    ]
}

#[test]
fn section_name_is_the_meld_contract() {
    // If this string ever changes, meld's emitter and scry's reader
    // disagree and projection silently disappears — pin it.
    assert_eq!(SECTION_NAME, "component-provenance");
    assert_eq!(&MAGIC, b"SCPV");
    assert_eq!(FORMAT_VERSION, 1);
}

#[test]
fn round_trip_is_lossless() {
    let origins = sample();
    let bytes = encode(&origins);
    let decoded = decode(&bytes).expect("round-trip decode must succeed");
    assert_eq!(
        decoded, origins,
        "decode(encode(x)) must equal x (FEAT-002 AC#5)"
    );
}

#[test]
fn empty_table_round_trips() {
    assert_eq!(decode(&encode(&[])), Ok(Vec::new()));
}

#[test]
fn projection_attributes_and_never_invents() {
    let origins = sample();

    // A mapped fused index resolves to its exact component origin.
    assert_eq!(
        project(&origins, 5),
        Some(ComponentOrigin {
            fused_func_index: 5,
            component_id: 1,
            orig_func_index: 0
        }),
        "projection must attribute fused func 5 to component 1 / func 0"
    );

    // Projection is keyed by fused-func-index, not position: index 6
    // (the 4th entry) resolves correctly.
    assert_eq!(
        project(&origins, 6),
        Some(ComponentOrigin {
            fused_func_index: 6,
            component_id: 1,
            orig_func_index: 1
        })
    );

    // Unmapped fused indices must yield None — never a fabricated
    // origin (the soundness property of attribution: scry never claims
    // a component source it cannot prove).
    assert_eq!(project(&origins, 2), None);
    assert_eq!(project(&origins, 4), None);
    assert_eq!(project(&origins, 100), None);
    assert_eq!(project(&[], 0), None);
}

#[test]
fn round_trips_through_a_real_wasm_custom_section() {
    // Build a minimal core module and append a real Wasm custom section
    // named `component-provenance` carrying the encoded payload, then
    // confirm the section name + payload survive the Wasm encoding and
    // decode back to the original table. This is the exact byte path the
    // analyzer's pre-pass walks: `reader.name() == SECTION_NAME` then
    // `decode(reader.data())`.
    let origins = sample();
    let payload = encode(&origins);

    // Smallest valid core module: the 8-byte header `\0asm` + version 1.
    let mut module: Vec<u8> = vec![0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00];
    // Custom section: id 0, then a size-prefixed body of
    // (name-len, name, payload).
    let name = SECTION_NAME.as_bytes();
    let mut body: Vec<u8> = Vec::new();
    write_uleb128(&mut body, name.len() as u64);
    body.extend_from_slice(name);
    body.extend_from_slice(&payload);
    module.push(0x00); // custom section id
    write_uleb128(&mut module, body.len() as u64);
    module.extend_from_slice(&body);

    // Walk the module with wasmparser exactly as the analyzer does and
    // pull the `component-provenance` section back out.
    let mut found: Option<Vec<ComponentOrigin>> = None;
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
        Some(origins),
        "the component-provenance custom section must survive Wasm encoding and decode losslessly"
    );
}

#[test]
fn decoder_rejects_malformed_payloads() {
    // Bad magic.
    let mut bad = encode(&sample());
    bad[0] = b'Z';
    assert!(matches!(decode(&bad), Err(DecodeError::BadMagic { .. })));

    // Unknown version.
    let mut bad = encode(&sample());
    bad[4] = 9;
    assert_eq!(
        decode(&bad),
        Err(DecodeError::UnsupportedVersion { found: 9 })
    );

    // Truncated body.
    let mut bad = encode(&sample());
    bad.truncate(bad.len() - 1);
    assert!(matches!(
        decode(&bad),
        Err(DecodeError::LengthMismatch { .. })
    ));

    // Trailing garbage.
    let mut bad = encode(&sample());
    bad.push(0x00);
    assert!(matches!(
        decode(&bad),
        Err(DecodeError::LengthMismatch { .. })
    ));

    // Too short for the header.
    assert!(matches!(
        decode(&[0x53, 0x43]),
        Err(DecodeError::TooShortForHeader { .. })
    ));
}

/// Minimal unsigned LEB128 writer — wasmparser reads sizes as LEB128, so
/// the test must encode the custom-section name length and body length
/// the same way. (We don't pull in `wasm-encoder` just for this.)
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

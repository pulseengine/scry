//! proof-audit: a kernel `Print Assumptions` audit over every theorem in a
//! Rocq proof tree (scry FEAT-105, #207).
//!
//! `generate` scans `*.v` files for theorem-like declarations and writes one
//! audit file that requires every module and runs `Print Assumptions` on each
//! declaration, preceded by a marker line. `check` re-scans the same tree,
//! reads the coqc output of that audit file and fails unless:
//!
//!   * at least one declaration exists (fail closed on an empty tree),
//!   * every declaration has exactly one audit block and no block is extra
//!     (completeness: audited == declared),
//!   * every block is "Closed under the global context" or lists only axioms
//!     named in the allow-list,
//!   * no block contains anything else (an unknown trust escape fails).
//!
//! Blind spots, stated so nobody reads more into a pass: only declarations
//! introduced by Theorem/Lemma/Corollary/Proposition/Fact/Remark/Example at
//! the start of a line are audited (not Definitions closed with `Defined`, not
//! Instances or Program obligations); Section `Variable`/`Hypothesis`
//! premises are discharged by generalisation and are NOT axioms, so they are
//! the trust-escape ledger's job, not this audit's.
//!
//! `ledger` reconciles `proofs/trust-ledger.tsv`: its `gen` rows must equal the
//! Section premises scanned from the sources plus the axioms in the audit
//! output, both directions; every proof file needs a `hand-mirror` row; every
//! hand row's file must exist; and against a baseline ledger the row count may
//! only grow when an `override` line names the new count. It cannot tell
//! whether a hand row is true, only that it is present.
//!
//! Exit codes: 0 pass, 1 audit failed, 2 usage or I/O error.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

const MARKER: &str = "@@PROOF-AUDIT ";
const KEYWORDS: [&str; 7] = [
    "Theorem",
    "Lemma",
    "Corollary",
    "Proposition",
    "Fact",
    "Remark",
    "Example",
];

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct Decl {
    module: String,
    name: String,
}

impl Decl {
    fn qualified(&self, prefix: &str) -> String {
        format!("{prefix}.{}.{}", self.module, self.name)
    }
}

/// Theorem-like declarations in one source file, in order.
fn scan_source(module: &str, text: &str) -> Vec<Decl> {
    let mut out = Vec::new();
    let stripped = strip_comments(text);
    for line in stripped.lines() {
        let t = line.trim_start();
        for kw in KEYWORDS {
            if let Some(rest) = t.strip_prefix(kw) {
                if !rest.starts_with(char::is_whitespace) {
                    continue;
                }
                let name: String = rest
                    .trim_start()
                    .chars()
                    .take_while(|c| c.is_alphanumeric() || *c == '_' || *c == '\'')
                    .collect();
                if !name.is_empty() {
                    out.push(Decl {
                        module: module.to_string(),
                        name,
                    });
                }
            }
        }
    }
    out
}

/// Remove Rocq comments `(* ... *)`, which nest.
fn strip_comments(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let b = text.as_bytes();
    let mut depth = 0usize;
    let mut i = 0;
    while i < b.len() {
        if i + 1 < b.len() && b[i] == b'(' && b[i + 1] == b'*' {
            depth += 1;
            i += 2;
            continue;
        }
        if depth > 0 && i + 1 < b.len() && b[i] == b'*' && b[i + 1] == b')' {
            depth -= 1;
            i += 2;
            continue;
        }
        if depth == 0 {
            out.push(b[i] as char);
        } else if b[i] == b'\n' {
            out.push('\n');
        }
        i += 1;
    }
    out
}

/// `(module, text)` for every `*.v` file directly under `dir`, sorted.
fn read_tree(dir: &Path) -> Result<Vec<(String, String)>, String> {
    let mut files: Vec<PathBuf> = fs::read_dir(dir)
        .map_err(|e| format!("reading {}: {e}", dir.display()))?
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().is_some_and(|x| x == "v"))
        .collect();
    files.sort();
    let mut out = Vec::new();
    for f in files {
        let module = f
            .file_stem()
            .and_then(|s| s.to_str())
            .ok_or_else(|| format!("bad file name {}", f.display()))?
            .to_string();
        let text = fs::read_to_string(&f).map_err(|e| format!("reading {}: {e}", f.display()))?;
        out.push((module, text));
    }
    Ok(out)
}

fn scan_tree(dir: &Path) -> Result<Vec<Decl>, String> {
    Ok(read_tree(dir)?
        .iter()
        .flat_map(|(m, t)| scan_source(m, t))
        .collect())
}

fn generate(decls: &[Decl], prefix: &str) -> String {
    let modules: BTreeSet<&str> = decls.iter().map(|d| d.module.as_str()).collect();
    let mut s = String::from("(* Generated by tools/proof-audit (FEAT-105). Do not edit. *)\n");
    for m in &modules {
        s.push_str(&format!("Require {prefix}.{m}.\n"));
    }
    for d in decls {
        let q = d.qualified(prefix);
        s.push_str(&format!(
            "Goal True. idtac \"{MARKER}{q}\". Abort.\nPrint Assumptions {q}.\n"
        ));
    }
    s
}

#[derive(Debug, PartialEq, Eq)]
enum Verdict {
    Closed,
    Axioms(Vec<String>),
    Unknown(String),
}

/// Split coqc output into marker-delimited blocks and classify each.
fn parse_output(out: &str) -> Result<BTreeMap<String, Vec<Verdict>>, String> {
    let mut blocks: BTreeMap<String, Vec<Verdict>> = BTreeMap::new();
    let mut current: Option<(String, Vec<String>)> = None;
    let flush = |cur: Option<(String, Vec<String>)>,
                 blocks: &mut BTreeMap<String, Vec<Verdict>>| {
        if let Some((name, lines)) = cur {
            blocks.entry(name).or_default().push(classify(&lines));
        }
    };
    for line in out.lines() {
        if let Some(pos) = line.find(MARKER) {
            let name = line[pos + MARKER.len()..].trim().to_string();
            flush(current.take(), &mut blocks);
            current = Some((name, Vec::new()));
        } else if let Some((_, lines)) = current.as_mut() {
            lines.push(line.to_string());
        } else if !line.trim().is_empty() {
            return Err(format!("output before the first audit marker: {line:?}"));
        }
    }
    flush(current.take(), &mut blocks);
    Ok(blocks)
}

fn classify(lines: &[String]) -> Verdict {
    let body: Vec<&str> = lines
        .iter()
        .map(|l| l.as_str())
        .filter(|l| !l.trim().is_empty())
        .collect();
    if body.is_empty() {
        return Verdict::Unknown("empty block (Print Assumptions printed nothing)".into());
    }
    if body.len() == 1 && body[0].trim() == "Closed under the global context" {
        return Verdict::Closed;
    }
    if body[0].trim() != "Axioms:" {
        return Verdict::Unknown(body[0].trim().to_string());
    }
    let mut axioms = Vec::new();
    for l in &body[1..] {
        if l.starts_with(char::is_whitespace) {
            continue; // continuation of a wrapped axiom type
        }
        match l.split_once(" :") {
            Some((name, _)) if !name.contains(' ') => axioms.push(name.to_string()),
            _ => return Verdict::Unknown(l.trim().to_string()),
        }
    }
    Verdict::Axioms(axioms)
}

#[derive(Debug, Default)]
struct Report {
    declared: usize,
    audited: usize,
    failures: Vec<String>,
}

fn check(
    decls: &[Decl],
    blocks: &BTreeMap<String, Vec<Verdict>>,
    allow: &BTreeSet<String>,
    prefix: &str,
) -> Report {
    let mut r = Report {
        declared: decls.len(),
        ..Default::default()
    };
    if decls.is_empty() {
        r.failures
            .push("no theorem declarations found: nothing was audited, which is not a pass".into());
        return r;
    }
    let mut expected = BTreeSet::new();
    for d in decls {
        let q = d.qualified(prefix);
        if !expected.insert(q.clone()) {
            r.failures.push(format!("declared twice: {q}"));
        }
    }
    for q in &expected {
        match blocks.get(q).map(|v| v.as_slice()) {
            None | Some([]) => r.failures.push(format!("not audited: {q}")),
            Some([v]) => {
                r.audited += 1;
                match v {
                    Verdict::Closed => {}
                    Verdict::Axioms(ax) => {
                        for a in ax {
                            if !allow.contains(a) {
                                r.failures
                                    .push(format!("{q} depends on axiom {a} (not allow-listed)"));
                            }
                        }
                    }
                    Verdict::Unknown(what) => r
                        .failures
                        .push(format!("{q}: unrecognised assumption output: {what}")),
                }
            }
            Some(_) => r.failures.push(format!("audited more than once: {q}")),
        }
    }
    for name in blocks.keys() {
        if !expected.contains(name) {
            r.failures
                .push(format!("audit block for an undeclared name: {name}"));
        }
    }
    r
}

fn read_allow(path: Option<&str>) -> Result<BTreeSet<String>, String> {
    let Some(p) = path else {
        return Ok(BTreeSet::new());
    };
    let text = fs::read_to_string(p).map_err(|e| format!("reading {p}: {e}"))?;
    Ok(text
        .lines()
        .map(|l| l.split('#').next().unwrap_or("").trim())
        .filter(|l| !l.is_empty())
        .map(String::from)
        .collect())
}

// ── trust-escape ledger ────────────────────────────────────────────────────
//
// One TSV file, `origin<TAB>kind<TAB>where<TAB>name<TAB>note` per row, `#`
// comments, and `override<TAB><count><TAB><reason>` lines. `gen` rows are
// regenerated here and must equal the file's `gen` rows in both directions;
// `hand` rows carry what no tool can derive. Against a baseline (main's
// ledger) the row count may only grow when an override names the new count.

const GEN_KINDS: [&str; 3] = ["section-variable", "section-hypothesis", "axiom"];
const HAND_KINDS: [&str; 4] = [
    "hand-mirror",
    "gamma-swept",
    "verus-assumption",
    "verus-fork-pin",
];

/// Section premises, by keyword, mapped to their ledger kind.
const PREMISES: [(&str, &str); 6] = [
    ("Variable", "section-variable"),
    ("Variables", "section-variable"),
    ("Parameter", "section-variable"),
    ("Parameters", "section-variable"),
    ("Hypothesis", "section-hypothesis"),
    ("Hypotheses", "section-hypothesis"),
];

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct Row {
    origin: String,
    kind: String,
    place: String,
    name: String,
    note: String,
}

impl Row {
    fn key(&self) -> (String, String, String) {
        (self.kind.clone(), self.place.clone(), self.name.clone())
    }
    fn tsv(&self) -> String {
        format!(
            "{}\t{}\t{}\t{}\t{}",
            self.origin, self.kind, self.place, self.name, self.note
        )
    }
}

/// Names bound by one premise line: `Variable a b : T.` or `Variables (a : T) (b : U).`
fn premise_names(rest: &str) -> Vec<String> {
    let ident = |s: &str| -> Vec<String> {
        s.split_whitespace()
            .filter(|w| {
                w.chars()
                    .all(|c| c.is_alphanumeric() || c == '_' || c == '\'')
            })
            .map(String::from)
            .collect()
    };
    let rest = rest.trim_start();
    if rest.starts_with('(') {
        let mut names = Vec::new();
        for group in rest.split('(').skip(1) {
            if let Some((lhs, _)) = group.split_once(':') {
                names.extend(ident(lhs));
            }
        }
        names
    } else {
        rest.split_once(':')
            .map(|(lhs, _)| ident(lhs))
            .unwrap_or_default()
    }
}

/// Generated rows from the sources: every Section premise. `Context` is not
/// parsed, so it is refused rather than silently skipped.
fn scan_premises(dir: &str, tree: &[(String, String)]) -> Result<Vec<Row>, String> {
    let mut rows = Vec::new();
    for (module, text) in tree {
        let place = format!("{dir}/{module}.v");
        for line in strip_comments(text).lines() {
            let t = line.trim_start();
            if t.strip_prefix("Context")
                .is_some_and(|r| r.starts_with(char::is_whitespace))
            {
                return Err(format!("{place}: `Context` is not parsed by the ledger; declare premises with Variable/Hypothesis"));
            }
            for (kw, kind) in PREMISES {
                let Some(rest) = t.strip_prefix(kw) else {
                    continue;
                };
                if !rest.starts_with(char::is_whitespace) {
                    continue;
                }
                let names = premise_names(rest);
                if names.is_empty() {
                    return Err(format!(
                        "{place}: cannot read the names in `{}`",
                        t.trim_end()
                    ));
                }
                for name in names {
                    rows.push(Row {
                        origin: "gen".into(),
                        kind: kind.into(),
                        place: place.clone(),
                        name,
                        note: String::new(),
                    });
                }
            }
        }
    }
    Ok(rows)
}

/// Generated rows from the audit output: every axiom any theorem depends on.
fn axiom_rows(blocks: &BTreeMap<String, Vec<Verdict>>) -> Vec<Row> {
    let names: BTreeSet<&String> = blocks
        .values()
        .flatten()
        .filter_map(|v| match v {
            Verdict::Axioms(a) => Some(a),
            _ => None,
        })
        .flatten()
        .collect();
    names
        .into_iter()
        .map(|n| Row {
            origin: "gen".into(),
            kind: "axiom".into(),
            place: "-".into(),
            name: n.clone(),
            note: String::new(),
        })
        .collect()
}

#[derive(Debug, Default)]
struct Ledger {
    rows: Vec<Row>,
    overrides: BTreeMap<usize, String>,
}

fn parse_ledger(text: &str) -> Result<Ledger, String> {
    let mut l = Ledger::default();
    for (i, raw) in text.lines().enumerate() {
        let n = i + 1;
        if raw.trim().is_empty() || raw.trim_start().starts_with('#') {
            continue;
        }
        let f: Vec<&str> = raw.split('\t').collect();
        if f[0] == "override" {
            let count = f
                .get(1)
                .and_then(|c| c.trim().parse::<usize>().ok())
                .ok_or(format!("line {n}: override needs a row count"))?;
            let reason = f.get(2).map(|r| r.trim()).unwrap_or("");
            if reason.is_empty() {
                return Err(format!("line {n}: override {count} needs a reason"));
            }
            l.overrides.insert(count, reason.to_string());
            continue;
        }
        if f.len() != 5 {
            return Err(format!(
                "line {n}: expected 5 tab-separated fields, found {}",
                f.len()
            ));
        }
        let row = Row {
            origin: f[0].into(),
            kind: f[1].into(),
            place: f[2].into(),
            name: f[3].into(),
            note: f[4].into(),
        };
        let kinds: &[&str] = match row.origin.as_str() {
            "gen" => &GEN_KINDS,
            "hand" => &HAND_KINDS,
            o => return Err(format!("line {n}: origin must be gen or hand, not {o:?}")),
        };
        if !kinds.contains(&row.kind.as_str()) {
            return Err(format!(
                "line {n}: kind {:?} is not a {} kind",
                row.kind, row.origin
            ));
        }
        if row.place.is_empty() || row.name.is_empty() {
            return Err(format!("line {n}: where and name must not be empty"));
        }
        l.rows.push(row);
    }
    Ok(l)
}

#[derive(Debug, Default)]
struct LedgerReport {
    generated: usize,
    hand: usize,
    baseline: Option<usize>,
    failures: Vec<String>,
}

/// `exists` answers whether a hand row's `where` path is present.
fn check_ledger(
    ledger: &Ledger,
    regenerated: &[Row],
    modules: &[String],
    dir: &str,
    baseline: Option<&Ledger>,
    exists: &dyn Fn(&str) -> bool,
) -> LedgerReport {
    let mut r = LedgerReport::default();
    if modules.is_empty() {
        r.failures.push(format!(
            "no .v files under {dir}: nothing to reconcile, which is not a pass"
        ));
        return r;
    }
    let mut seen = BTreeSet::new();
    for row in &ledger.rows {
        if !seen.insert(row.key()) {
            r.failures.push(format!("duplicate row: {}", row.tsv()));
        }
    }
    let have: BTreeSet<_> = ledger
        .rows
        .iter()
        .filter(|x| x.origin == "gen")
        .map(Row::key)
        .collect();
    let want: BTreeSet<_> = regenerated.iter().map(Row::key).collect();
    for row in regenerated {
        if !have.contains(&row.key()) {
            r.failures.push(format!(
                "generated but not in the ledger (add this row): {}",
                row.tsv()
            ));
        }
    }
    for row in ledger.rows.iter().filter(|x| x.origin == "gen") {
        if !want.contains(&row.key()) {
            r.failures.push(format!(
                "in the ledger but no longer generated (remove this row): {}",
                row.tsv()
            ));
        }
    }
    let hand: Vec<&Row> = ledger.rows.iter().filter(|x| x.origin == "hand").collect();
    for row in &hand {
        if !exists(&row.place) {
            r.failures
                .push(format!("hand row points at a missing file: {}", row.tsv()));
        }
    }
    // Every proof file is a hand-written model until shown otherwise: each one
    // has a hand-mirror row, and each hand-mirror row names a proof file.
    let mirrored: BTreeSet<&str> = hand
        .iter()
        .filter(|x| x.kind == "hand-mirror")
        .map(|x| x.place.as_str())
        .collect();
    let files: BTreeSet<String> = modules.iter().map(|m| format!("{dir}/{m}.v")).collect();
    for f in &files {
        if !mirrored.contains(f.as_str()) {
            r.failures
                .push(format!("proof file without a hand-mirror row: {f}"));
        }
    }
    for m in &mirrored {
        if !files.contains(*m) {
            r.failures.push(format!(
                "hand-mirror row for a file that is not a proof under {dir}: {m}"
            ));
        }
    }
    r.generated = have.len();
    r.hand = hand.len();
    if let Some(b) = baseline {
        let (now, before) = (ledger.rows.len(), b.rows.len());
        r.baseline = Some(before);
        if now > before && !ledger.overrides.contains_key(&now) {
            r.failures.push(format!(
                "the ledger grew from {before} to {now} rows with no recorded override; add `override<TAB>{now}<TAB><reason>`"
            ));
        }
    }
    r
}

const USAGE: &str = "usage:
  proof-audit generate --proofs <dir> --prefix <logical.prefix> --out <file.v>
  proof-audit check    --proofs <dir> --prefix <logical.prefix> --output <coqc-output> [--allow <file>] [--format text|json]
  proof-audit ledger   --proofs <dir> --output <coqc-output> --ledger <file.tsv> [--baseline <file.tsv>] [--format text|json]
  proof-audit --version | --help";

fn arg<'a>(args: &'a [String], flag: &str) -> Option<&'a str> {
    args.iter()
        .position(|a| a == flag)
        .and_then(|i| args.get(i + 1))
        .map(|s| s.as_str())
}

fn run(args: &[String]) -> Result<bool, String> {
    let known = [
        "--proofs",
        "--prefix",
        "--out",
        "--output",
        "--allow",
        "--format",
        "--ledger",
        "--baseline",
    ];
    let mut i = 1;
    while i < args.len() {
        let a = args[i].as_str();
        if a.starts_with("--") {
            if !known.contains(&a) {
                return Err(format!("unknown flag {a}\n{USAGE}"));
            }
            i += 2;
        } else {
            return Err(format!("unexpected argument {a}\n{USAGE}"));
        }
    }
    let proofs = arg(args, "--proofs").ok_or("missing --proofs")?;
    if args[0] == "ledger" {
        return run_ledger(args, proofs);
    }
    let prefix = arg(args, "--prefix").ok_or("missing --prefix")?;
    let decls = scan_tree(Path::new(proofs))?;
    match args[0].as_str() {
        "generate" => {
            let out = arg(args, "--out").ok_or("missing --out")?;
            if decls.is_empty() {
                return Err(format!("no theorem declarations under {proofs}"));
            }
            fs::write(out, generate(&decls, prefix)).map_err(|e| format!("writing {out}: {e}"))?;
            println!("proof-audit: wrote {} audit entries to {out}", decls.len());
            Ok(true)
        }
        "check" => {
            let output = arg(args, "--output").ok_or("missing --output")?;
            let text = fs::read_to_string(output).map_err(|e| format!("reading {output}: {e}"))?;
            let blocks = parse_output(&text)?;
            let allow = read_allow(arg(args, "--allow"))?;
            let r = check(&decls, &blocks, &allow, prefix);
            let ok = r.failures.is_empty();
            if arg(args, "--format") == Some("json") {
                let fails: Vec<String> = r
                    .failures
                    .iter()
                    .map(|f| format!("\"{}\"", f.replace('\\', "\\\\").replace('"', "\\\"")))
                    .collect();
                println!(
                    "{{\"declared\":{},\"audited\":{},\"allow_listed_axioms\":{},\"pass\":{},\"failures\":[{}]}}",
                    r.declared,
                    r.audited,
                    allow.len(),
                    ok,
                    fails.join(",")
                );
            } else {
                for f in &r.failures {
                    println!("FAIL: {f}");
                }
                println!(
                    "proof-audit: declared {}, audited {}, allow-listed axioms {}: {}",
                    r.declared,
                    r.audited,
                    allow.len(),
                    if ok { "PASS" } else { "FAIL" }
                );
            }
            Ok(ok)
        }
        other => Err(format!("unknown command {other}\n{USAGE}")),
    }
}

fn read_ledger(path: &str) -> Result<Ledger, String> {
    let text = fs::read_to_string(path).map_err(|e| format!("reading {path}: {e}"))?;
    parse_ledger(&text).map_err(|e| format!("{path}: {e}"))
}

fn run_ledger(args: &[String], proofs: &str) -> Result<bool, String> {
    let output = arg(args, "--output").ok_or("missing --output")?;
    let ledger = read_ledger(arg(args, "--ledger").ok_or("missing --ledger")?)?;
    let baseline = arg(args, "--baseline").map(read_ledger).transpose()?;
    let tree = read_tree(Path::new(proofs))?;
    let modules: Vec<String> = tree.iter().map(|(m, _)| m.clone()).collect();
    let text = fs::read_to_string(output).map_err(|e| format!("reading {output}: {e}"))?;
    let mut regenerated = scan_premises(proofs, &tree)?;
    regenerated.extend(axiom_rows(&parse_output(&text)?));
    let exists = |p: &str| Path::new(p).exists();
    let r = check_ledger(
        &ledger,
        &regenerated,
        &modules,
        proofs,
        baseline.as_ref(),
        &exists,
    );
    let ok = r.failures.is_empty();
    let base = r.baseline.map_or("none".to_string(), |b| b.to_string());
    if arg(args, "--format") == Some("json") {
        let fails: Vec<String> = r
            .failures
            .iter()
            .map(|f| {
                format!(
                    "\"{}\"",
                    f.replace('\\', "\\\\")
                        .replace('"', "\\\"")
                        .replace('\t', "\\t")
                )
            })
            .collect();
        println!(
            "{{\"rows\":{},\"generated\":{},\"hand\":{},\"baseline\":{},\"pass\":{},\"failures\":[{}]}}",
            ledger.rows.len(),
            r.generated,
            r.hand,
            r.baseline.map_or("null".to_string(), |b| b.to_string()),
            ok,
            fails.join(",")
        );
    } else {
        for f in &r.failures {
            println!("FAIL: {f}");
        }
        println!(
            "proof-audit ledger: {} rows ({} generated, {} hand), baseline {base}: {}",
            ledger.rows.len(),
            r.generated,
            r.hand,
            if ok { "PASS" } else { "FAIL" }
        );
    }
    Ok(ok)
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args.first().map(|s| s.as_str()) {
        Some("--version") | Some("-V") => {
            println!("proof-audit {}", env!("CARGO_PKG_VERSION"));
            return ExitCode::SUCCESS;
        }
        Some("--help") | Some("-h") | None => {
            println!("{USAGE}");
            return if args.is_empty() {
                ExitCode::from(2)
            } else {
                ExitCode::SUCCESS
            };
        }
        _ => {}
    }
    match run(&args) {
        Ok(true) => ExitCode::SUCCESS,
        Ok(false) => ExitCode::from(1),
        Err(e) => {
            eprintln!("proof-audit: {e}");
            ExitCode::from(2)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn decls(src: &str) -> Vec<Decl> {
        scan_source("M", src)
    }

    #[test]
    fn scans_keywords_and_skips_comments_and_lets() {
        let d = decls(
            "Theorem a : True.\n  Lemma b' : True.\n(* Lemma hidden : True. (* nested *) *)\nLet c := 1.\nDefinition d := 2.\nCorollary e: True.\nLemmaX f : True.\n",
        );
        let names: Vec<&str> = d.iter().map(|d| d.name.as_str()).collect();
        assert_eq!(names, ["a", "b'", "e"]);
    }

    fn run_check(out: &str, allow: &[&str]) -> Report {
        let d = vec![
            Decl {
                module: "M".into(),
                name: "a".into(),
            },
            Decl {
                module: "M".into(),
                name: "b".into(),
            },
        ];
        let blocks = parse_output(out).unwrap();
        let allow = allow.iter().map(|s| s.to_string()).collect();
        check(&d, &blocks, &allow, "p")
    }

    const CLOSED_BOTH: &str = "@@PROOF-AUDIT p.M.a\nClosed under the global context\n@@PROOF-AUDIT p.M.b\nClosed under the global context\n";

    #[test]
    fn all_closed_passes() {
        let r = run_check(CLOSED_BOTH, &[]);
        assert!(r.failures.is_empty(), "{:?}", r.failures);
        assert_eq!((r.declared, r.audited), (2, 2));
    }

    #[test]
    fn planted_axiom_fails_unless_allow_listed() {
        let out = "@@PROOF-AUDIT p.M.a\nAxioms:\nplanted : False\n@@PROOF-AUDIT p.M.b\nClosed under the global context\n";
        assert_eq!(run_check(out, &[]).failures.len(), 1);
        assert!(run_check(out, &["planted"]).failures.is_empty());
    }

    #[test]
    fn wrapped_axiom_type_is_one_axiom() {
        let out = "@@PROOF-AUDIT p.M.a\nAxioms:\nclassic : forall P : Prop,\n          P \\/ ~ P\n@@PROOF-AUDIT p.M.b\nClosed under the global context\n";
        let r = run_check(out, &["classic"]);
        assert!(r.failures.is_empty(), "{:?}", r.failures);
    }

    #[test]
    fn missing_block_fails_completeness() {
        let out = "@@PROOF-AUDIT p.M.a\nClosed under the global context\n";
        let r = run_check(out, &[]);
        assert_eq!(r.failures, ["not audited: p.M.b"]);
    }

    #[test]
    fn duplicate_and_extra_blocks_fail() {
        let dup = format!("{CLOSED_BOTH}@@PROOF-AUDIT p.M.a\nClosed under the global context\n");
        assert!(run_check(&dup, &[])
            .failures
            .iter()
            .any(|f| f.contains("more than once")));
        let extra = format!("{CLOSED_BOTH}@@PROOF-AUDIT p.M.z\nClosed under the global context\n");
        assert!(run_check(&extra, &[])
            .failures
            .iter()
            .any(|f| f.contains("undeclared")));
    }

    #[test]
    fn unknown_and_empty_output_fail_closed() {
        let unknown = "@@PROOF-AUDIT p.M.a\nConstants relying on type-in-type:\nfoo\n@@PROOF-AUDIT p.M.b\nClosed under the global context\n";
        assert!(run_check(unknown, &[]).failures[0].contains("unrecognised"));
        let empty = "@@PROOF-AUDIT p.M.a\n@@PROOF-AUDIT p.M.b\nClosed under the global context\n";
        assert!(run_check(empty, &[]).failures[0].contains("empty block"));
    }

    #[test]
    fn no_declarations_is_not_a_pass() {
        let r = check(&[], &BTreeMap::new(), &BTreeSet::new(), "p");
        assert_eq!(r.failures.len(), 1);
    }

    #[test]
    fn stray_output_before_first_marker_is_an_error() {
        assert!(parse_output(
            "Warning: something\n@@PROOF-AUDIT p.M.a\nClosed under the global context\n"
        )
        .is_err());
    }

    #[test]
    fn generated_file_audits_every_declaration() {
        let d = vec![
            Decl {
                module: "A".into(),
                name: "x".into(),
            },
            Decl {
                module: "B".into(),
                name: "y".into(),
            },
        ];
        let g = generate(&d, "proofs.rocq");
        assert!(g.contains("Require proofs.rocq.A.\nRequire proofs.rocq.B.\n"));
        assert_eq!(g.matches("Print Assumptions ").count(), 2);
        assert_eq!(g.matches(MARKER).count(), 2);
    }

    // ── ledger ──

    const SRC: &str = "Section S.\nVariable node : Type.\nVariables a b : nat.\nVariables (c : nat) (d e : bool).\n(* Hypothesis hidden : False. *)\nHypothesis h : a = b.\nEnd S.\n";

    fn tree() -> Vec<(String, String)> {
        vec![("A".into(), SRC.into())]
    }

    fn regen() -> Vec<Row> {
        scan_premises("p", &tree()).unwrap()
    }

    const GOOD: &str = "# comment\n\
gen\tsection-variable\tp/A.v\tnode\t\n\
gen\tsection-variable\tp/A.v\ta\t\n\
gen\tsection-variable\tp/A.v\tb\t\n\
gen\tsection-variable\tp/A.v\tc\t\n\
gen\tsection-variable\tp/A.v\td\t\n\
gen\tsection-variable\tp/A.v\te\t\n\
gen\tsection-hypothesis\tp/A.v\th\tpremise of every lemma in S\n\
hand\thand-mirror\tp/A.v\tA\tmodel of foo\n";

    fn run_ledger_check(text: &str, base: Option<&str>) -> LedgerReport {
        let l = parse_ledger(text).unwrap();
        let b = base.map(|t| parse_ledger(t).unwrap());
        check_ledger(&l, &regen(), &["A".to_string()], "p", b.as_ref(), &|_| true)
    }

    #[test]
    fn premises_are_scanned_in_both_binder_forms() {
        let names: Vec<(String, String)> = regen().into_iter().map(|r| (r.kind, r.name)).collect();
        let n: Vec<&str> = names.iter().map(|(_, n)| n.as_str()).collect();
        assert_eq!(n, ["node", "a", "b", "c", "d", "e", "h"]);
        assert_eq!(names[6].0, "section-hypothesis");
    }

    #[test]
    fn context_is_refused_not_skipped() {
        let t = vec![(
            "A".to_string(),
            "Section S.\nContext (x : nat).\nEnd S.\n".to_string(),
        )];
        assert!(scan_premises("p", &t).is_err());
    }

    #[test]
    fn matching_ledger_passes() {
        let r = run_ledger_check(GOOD, Some(GOOD));
        assert!(r.failures.is_empty(), "{:?}", r.failures);
        assert_eq!((r.generated, r.hand, r.baseline), (7, 1, Some(8)));
    }

    #[test]
    fn missing_and_stale_generated_rows_fail() {
        let missing = GOOD.replace(
            "gen\tsection-hypothesis\tp/A.v\th\tpremise of every lemma in S\n",
            "",
        );
        let r = run_ledger_check(&missing, None);
        assert!(
            r.failures
                .iter()
                .any(|f| f.contains("not in the ledger") && f.contains("\th\t")),
            "{:?}",
            r.failures
        );
        let stale = format!("{GOOD}gen\tsection-variable\tp/A.v\tgone\t\n");
        let r = run_ledger_check(&stale, None);
        assert!(
            r.failures
                .iter()
                .any(|f| f.contains("no longer generated") && f.contains("gone")),
            "{:?}",
            r.failures
        );
    }

    #[test]
    fn growth_needs_an_override_naming_the_new_count() {
        let grown = format!("{GOOD}hand\tgamma-swept\tp/A.v\tadd\tw=8\n");
        let r = run_ledger_check(&grown, Some(GOOD));
        assert!(
            r.failures.iter().any(|f| f.contains("grew from 8 to 9")),
            "{:?}",
            r.failures
        );
        let wrong = format!("{grown}override\t10\tstale count\n");
        assert!(!run_ledger_check(&wrong, Some(GOOD)).failures.is_empty());
        let ok = format!("{grown}override\t9\tnew gamma-swept transfer, FEAT-x\n");
        let r = run_ledger_check(&ok, Some(GOOD));
        assert!(r.failures.is_empty(), "{:?}", r.failures);
        let shrunk = GOOD.replace("gen\tsection-variable\tp/A.v\tnode\t\n", "");
        let r = run_ledger_check(&shrunk, Some(GOOD));
        assert!(
            r.failures.iter().all(|f| !f.contains("grew")),
            "{:?}",
            r.failures
        );
    }

    #[test]
    fn every_proof_file_needs_a_hand_mirror_row() {
        let no_mirror = GOOD.replace("hand\thand-mirror\tp/A.v\tA\tmodel of foo\n", "");
        let r = run_ledger_check(&no_mirror, None);
        assert!(
            r.failures
                .iter()
                .any(|f| f.contains("without a hand-mirror row: p/A.v")),
            "{:?}",
            r.failures
        );
        let extra = format!("{GOOD}hand\thand-mirror\tp/B.v\tB\tx\n");
        let r = run_ledger_check(&extra, None);
        assert!(
            r.failures
                .iter()
                .any(|f| f.contains("not a proof under p: p/B.v")),
            "{:?}",
            r.failures
        );
    }

    #[test]
    fn malformed_rows_and_missing_files_fail() {
        assert!(parse_ledger("gen\taxiom\t-\tx\n").is_err(), "4 fields");
        assert!(
            parse_ledger("hand\taxiom\t-\tx\t\n").is_err(),
            "gen kind on a hand row"
        );
        assert!(parse_ledger("oops\taxiom\t-\tx\t\n").is_err(), "bad origin");
        assert!(
            parse_ledger("override\t3\t\n").is_err(),
            "override without reason"
        );
        let l = parse_ledger(GOOD).unwrap();
        let r = check_ledger(&l, &regen(), &["A".to_string()], "p", None, &|_| false);
        assert!(
            r.failures.iter().any(|f| f.contains("missing file")),
            "{:?}",
            r.failures
        );
        let r = check_ledger(&l, &regen(), &[], "p", None, &|_| true);
        assert!(
            r.failures.iter().any(|f| f.contains("not a pass")),
            "{:?}",
            r.failures
        );
    }

    #[test]
    fn axioms_from_the_audit_are_generated_rows() {
        let blocks = parse_output("@@PROOF-AUDIT p.M.a\nAxioms:\nfunext : forall x, x\n@@PROOF-AUDIT p.M.b\nAxioms:\nfunext : forall x, x\n").unwrap();
        let rows = axiom_rows(&blocks);
        assert_eq!(rows.len(), 1);
        assert_eq!(
            (rows[0].kind.as_str(), rows[0].name.as_str()),
            ("axiom", "funext")
        );
    }
}

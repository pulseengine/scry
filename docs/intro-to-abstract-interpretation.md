---
id: DOC-INTRO-AI
title: A friendly introduction to abstract interpretation (and what scry does with it)
type: explainer
status: draft
tags: [intro, abstract-interpretation, soundness, education]
---

# A friendly introduction to abstract interpretation

> Audience: you're a developer, comfortable with code, never had a
> formal-methods class. You've heard "abstract interpretation"
> mentioned in passing and want to understand what it actually is
> before reading anything else about scry.
>
> Time to read: ~10 minutes. No prior math required.

## 1. The everyday problem

Imagine you wrote this small function:

```c
int safe_index(int n) {
    if (n < 0) return 0;
    if (n > 1000) return 1000;
    return n;
}
```

Easy question: **after `safe_index` returns, can the result ever be
negative?** Obviously not — you can read the code and reason: the
first `if` catches negatives. So no.

Now imagine the function is 50,000 lines spread across 200 files,
calling deep into libraries you didn't write, with loops, recursion,
indirect calls, and inputs that come from the outside world.

Can the result of the function on line 47,213 ever be negative?

You don't know. Neither does your test suite — tests can only show
that the inputs you happened to pick didn't make it negative. They
say nothing about the inputs you didn't pick.

**Abstract interpretation is the discipline of answering questions
like that, automatically, for all possible inputs at once.**

## 2. The trick — values become sets of possible values

Concrete execution runs your program on *one* value at a time:

```
n = 5
  → return 5
n = -3
  → return 0
n = 9999
  → return 1000
```

Each run tells you about one input. To learn about *all* inputs, you'd
have to run it on all of them. For a 32-bit integer, that's 4 billion
runs — and that's just for `int`. Add a string and you're done.

The abstract trick: don't track *one* value, track the *set of values
that could be there*.

```
n ∈ [-∞, +∞]                                 (n is some int, we know nothing)
  if (n < 0) return 0                       (branch splits the set)
    in true branch: n ∈ [-∞, -1] → return 0   (result here ∈ {0})
    in false branch: n ∈ [0, +∞]            (carry forward the narrower set)
  if (n > 1000) return 1000
    in true branch: n ∈ [1001, +∞] → return 1000  (result here ∈ {1000})
    in false branch: n ∈ [0, 1000] → return n     (result here ∈ [0, 1000])

after the function, result ∈ {0} ∪ {1000} ∪ [0, 1000]
                          = [0, 1000]
```

We just proved, **for every possible input simultaneously**, that the
result is in `[0, 1000]`. No tests needed.

## 3. The abstract domain — what kind of "set" we use

We can't literally store every possible integer. Instead we pick a
*shape* for the sets we care about. That shape is called the
**abstract domain**. For numbers, popular ones include:

- **Interval**: just a lower and upper bound, e.g. `[0, 1000]`. Cheap
  to compute, can't express "n is in {3, 17, or 42}".
- **Octagon**: pairs of variables related, e.g. "x + y ≤ 10". More
  expressive, more expensive.
- **Constants**: "n is exactly 5" or "we don't know". The simplest
  useful domain.

Every abstract domain has the same three jobs:
1. **Express** what we know about a value (e.g. "n is in `[0, 1000]`").
2. **Combine** two facts when control-flow joins (e.g. when an `if`
   branches back together, the result set is the union).
3. **Transfer functions** — for every operation in the source
   language, say what the operation does *to abstract values*. E.g.
   `[a, b] + [c, d] = [a+c, b+d]` (for interval domain on integers).

For scry's v0.1 the domain is **intervals on i32 and i64 integers**.
That's enough to express "this counter is between 0 and 255" or
"this memory offset is between 4 and 4095" — useful properties for
catching bugs *or* for telling a compiler "you can skip this
bounds check, I already proved the access is in range."

## 4. The word "sound" — and why it matters

Here's the trap: it's very easy to write something that *looks*
like an abstract interpreter but quietly **misses real behavior**.
For example, if you forget to handle one branch of an `if`, your
analyzer reports "the result is always in `[0, 100]`" — but you
missed the case where it's actually `-5`, and now someone trusts
your analyzer's answer and writes a bounds check on `[0, 100]` and
the program crashes.

**Sound** means: if the analyzer says "all reachable behaviors are
in set X", then *every* real behavior is in X. The analyzer might
report some behaviors that can't actually happen (called *false
alarms*) — but it can never miss real ones.

Concretely, given a function `f`:

```
For every input i that f could see:
    the concrete result f(i) must be in the abstract result the analyzer computed
```

This is the *one* property that makes abstract interpretation
useful for safety-critical work. An unsound analyzer is worse than
no analyzer: it gives you false confidence. A sound one tells you
exactly what it knows and is honest about what it doesn't.

The price of soundness is *precision*. A sound analyzer is allowed
to say "this value could be anything" when it can't figure out the
real answer. That's annoying (lots of false alarms) but it's
truthful. Improving precision without losing soundness is the
research field's main job.

## 5. The infinite loop problem — and widening

You might wonder: what about loops?

```c
int x = 0;
while (some_condition()) {
    x = x + 1;
}
```

After one iteration, `x ∈ [0, 1]`. After two, `[0, 2]`. After
three, `[0, 3]`. The set keeps growing. If we naively iterate the
analysis, it never terminates.

The fix is **widening**: at loop headers, if we see the set is
growing without an obvious upper bound, we jump straight to `[0,
+∞]`. We give up precision to guarantee termination. It's sound
(we never lose real behaviors) but we lose the ability to say
"x is at most 1000" if the analyzer can't quickly prove the loop
terminates earlier.

Smart widening operators are an active research area. scry's v0.1
widening is the simple Cousot–Cousot variant: at each loop iteration,
if the lower bound dropped or the upper bound rose compared to last
time, push that side to ∞. After a few iterations the analysis
either stabilizes or hits ⊤ (the "anything" set), and we move on.

## 6. Where this comes from

The mathematical framework was set down by **Patrick and Radhia
Cousot in 1977** — a single POPL paper called *"Abstract
interpretation: a unified lattice model for static analysis of
programs by construction or approximation of fixpoints"* ([[AC-001]]
in our rivet artifact graph). That paper introduced the lattice
view, the Galois connection between concrete and abstract, the
widening idea, and the soundness theorem we still cite today.

The framework was applied industrially via tools like
[Astrée](https://www.absint.com/astree/index.htm), used by Airbus to
verify zero runtime errors in flight-control software for the A380.
That's the existence proof that abstract interpretation, done
seriously, scales to safety-critical software with industrial
confidence.

For WebAssembly specifically, the field is young (post-2020). See
the [README](../README.md) "prior art" section and `artifacts/research.yaml`
for the eleven papers our work builds on.

## 7. What scry does

scry applies abstract interpretation to **WebAssembly modules**:
the compiled bytecode produced by tools like Rust, C++, AssemblyScript,
or Go targeting `wasm32-wasip2`. We do this *sound*, against the
official Wasm operational semantics ([[AC-002]]), so the safety
case can name what scry proves and what it doesn't.

The v0.1 scry can:

- Take a Wasm Core Model module as input.
- Walk every reachable instruction in every reachable function.
- For each `i32` and `i64` local, compute the interval of values
  it could hold at every program point.
- Emit those intervals as a JSON invariant bundle.
- (Coming soon — see [[FEAT-001]] acceptance criterion #3.) Verify
  end-to-end that running the program on any concrete input
  produces values inside the abstract intervals scry computed.

That last bullet is the **soundness test in practice**: pick some
concrete inputs, run the program for real, check that every value
the program touches is inside the abstract interval scry predicted.
If we ever find a real value outside an abstract interval, scry has
a bug — and we want to know.

Later versions add:

- **Region-based memory model** ([[FEAT-005]]) — track which region
  each pointer is into, so the analyzer can say "load at offset
  `[4, 8]` from heap region `H1` is in-bounds" rather than
  collapsing all memory into one giant interval.
- **Sound call graph for `call_indirect`** ([[FEAT-006]]) — currently
  unsound across most Wasm analyzers per [[MF-003]]; scry's v0.3
  computes call targets under the same interval analysis on the
  operand stack ([[AC-008]]).
- **Compositional summaries** ([[FEAT-007]]) — analyze each function
  once, reuse the summary at every call site. Scales to fused
  modules from meld.
- **Optimizer integration** ([[FEAT-008]]) — feed scry's invariants
  to loom so it can elide bounds checks and fold constants the
  optimizer otherwise wouldn't dare touch.
- **Component-Model handle lifetimes** ([[FEAT-002]]) — track
  owned/borrowed `resource` handles at link time, catching
  use-after-drop before runtime.
- **Mechanized soundness** ([[FEAT-010]]) — full Rocq proof against
  WasmCert-Coq for the interval domain, so the soundness claim
  isn't paper-only.

## 8. The one-paragraph summary

Abstract interpretation runs your program over **sets** of possible
values instead of one value at a time, so you learn about every
possible input simultaneously. The "set" is shaped by an abstract
domain (intervals, octagons, regions) chosen to be cheap enough to
compute but expressive enough to prove what you care about.
**Sound** means the analyzer never misses real behaviors — false
alarms are allowed; missed behaviors are not. scry brings sound
abstract interpretation to WebAssembly so the PulseEngine pipeline
can earn the third DO-333 technique-class credit alongside the
deductive proofs (Verus, Rocq) and bounded model checking (Kani)
the rest of the stack already provides.

## 9. Where to go next

- Read [`docs/architecture.md`](architecture.md) for the *how* —
  the two-component build, the WIT cross-import, the WAC
  composition, all with mermaid diagrams.
- Read [`docs/roadmap.md`](roadmap.md) for the per-version plan.
- Read the [README](../README.md) "is this for you?" section to
  decide if scry is the tool you need.
- For the deeper academic foundations, the references in
  `artifacts/research.yaml` are scored 1-5 for direct relevance.
  Start with [[AC-001]] (the Cousot 1977 paper), then
  [[AC-006]] (Brandl et al. ECOOP 2023 — the closest modern
  precursor to scry).

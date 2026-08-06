# reverse-mathlib-foundation

An **external checked bridge** between
[reverse-mathlib](https://github.com/cameronfreer/reverse-mathlib) (the Turing-ideal
ω layer, frozen) and
[FormalizedFormalLogic/Foundation](https://github.com/FormalizedFormalLogic/Foundation)
(second-order Tarski semantics). It is **not** a component of either project: neither
core repository depends on the other, and this workspace depends on both at exact
pinned revisions (see `lakefile.toml`), on Foundation's toolchain, with narrow
Foundation imports only — never `import Foundation`. No changes to either core are
made from here.

## What is proved

**F1 — semantic adequacy (forward direction) and the ω-model countermodel.**

- `Rca0Theory`: the explicit semantic RCA₀ theory on ω-structures (basic axioms, Σ⁰₁
  induction, Δ⁰₁ comprehension as explicit theory obligations).
- `forward_adequacy`: every Turing ideal satisfies every axiom of `Rca0Theory` —
  built through an executable Δ⁰₀ evaluator, Tarski agreement, bounded oracle
  recursion, Σ⁰₁ stage / Π⁰₁ costage predicates, and a dovetailed Δ⁰₁ decision.
  **One-way realization evidence only**: the converse (realizers are ideals) is
  deliberately absent.
- `wklSentence` and `models_wklSentence_iff`: the exact binary-tree ŴKL sentence over
  the frozen `seqCode` coding, with an **unconditional** adapter — for arbitrary `Ω`,
  satisfaction is exactly the frozen `WeakKonigAt Ω`. The coding is arithmetized via
  Gödel's β (mathlib's `Nat.beta`).
- `rca0_not_semantically_implies_wkl`: the checked REC countermodel — one structure
  satisfies every `Rca0Theory` axiom and falsifies `wklSentence` (via the frozen
  Kleene tree).

**F3 — a Henkin-safe calculus and calculus-relative nonderivability.**

- `Derivable`: a bridge-local Hilbert-style calculus over open matrices whose open set
  slots are read universally over the designated second-order part. Second-order
  existential introduction is **from an open set slot only**; no rule manufactures a
  set, so comprehension enters only through the axiom set. Foundation's LK
  formula-witness rule (comprehension built into the logic) is deliberately not used.
- `soundness` / `soundness_sentence`: sound for **every** `Struc₂ ℒₒᵣ` — arbitrary
  domain, interpretation, and designated second-order part.
- `rca0_not_derives_wkl`: `Rca0Theory ⊬ wklSentence` **in this calculus**.
  *Proof-system-adequacy debt, recorded*: `Derivable` is not yet proved equivalent to
  any pinned standard proof system, so this never renders as an unqualified
  Simpson-style RCA₀ ⊬ WKL. No completeness claim is made anywhere.

**F2 — exact EFILC and one-sided Hall adapters, and ideal-level transfers.**

- `efilcSentence` / `models_efilcSentence_iff` and `hallSentence` /
  `models_hallSentence_iff`: exact sentences against the frozen
  `InternalInverseSystem` and `InternalHallFamily` presentations (the Hall marriage
  condition arithmetized as coded lists, proved equivalent to the frozen
  `Finset`-and-witness reading by `marriage_char`), both adapters **unconditional**.
- `SentenceTransfer`: EFILC ↔ ŴKL and EFILC → Hall at every Turing ideal, via the
  three frozen certified transformations; the ŴKL → Hall composition is flagged
  derived-only. `rca0_not_semantically_implies_efilc` is the EFILC countermodel.

## The export surface

`RMFoundationBridge/ExportSurface.lean` is the only export contract: **typed** records
(`ContextRealizationCertificate` — direction `forward`, status `realizationOnly`;
three `StatementAdapterCertificate`s — `unconditional`; `CalculusRecord` — id
`henkinSafeV1`, comparison `pending`; `NonderivabilityCertificate` — structurally
keyed to the calculus id). Downstream consumers cite these records and nothing else.

The reverse-mathlib certified scoreboard (ω-model: 3 / all-model: 0 / syntactic: 0)
is unaffected by anything here — adequacy evidence upgrades interpretation status; it
is not another mathematical leaf.

## Verification

- `lake build` — the full rollup, `warningAsError` on.
- `lake env lean scripts/Audit.lean` — axiom sweep (standard three only, every
  bridge-owned declaration including private/auxiliary) plus per-headline dependency
  gates: each gated theorem and export record must reach its named load-bearing
  dependencies, and no export leaf may reach the derived composition.

Both run in CI on every push.

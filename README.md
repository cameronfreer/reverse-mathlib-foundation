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

## How it works

reverse-mathlib's ω layer states *capabilities at a second-order part* — `WeakKonigAt Ω`,
`EFILCAt Ω`, `CountableHallAt Ω` are ordinary propositions about a collection of subsets
of ℕ — and certifies facts about Turing ideals. But that layer has no formal language:
"REC is a model of RCA₀" is not even sayable there. Foundation has the language and the
Tarski semantics, and knows nothing about reverse-mathlib. This bridge proves that the
frozen ω-objects **are** the models and satisfaction relations of genuine L₂ sentences,
in five moves:

1. **The structure.** `OmegaPart.toFoundation` packages `Ω` as a Foundation `Struc₂`:
   number sort standard ℕ under an explicitly *verified* interpretation, set sort exactly
   `Ω.sets`. Satisfaction is **definitionally** Tarski evaluation with set quantifiers
   ranging over `Ω.sets` — models are never constructed, only unfolded.
2. **The theory and the one hard axiom.** `Rca0Theory`'s basic axioms and Σ⁰₁-induction
   hold over *any* second-order part, because the first-order part is standard ℕ. The
   Turing-ideal hypothesis is consumed in exactly one place — Δ⁰₁ comprehension — where a
   computability chain (executable Δ⁰₀ evaluator ∥ Tarski agreement ∥ relative
   computability, meeting in Σ⁰₁ stage predicates and a dovetailed Δ⁰₁ decision) shows
   the defined set is Turing-reducible to the parameters, hence in the ideal.
3. **The adapters.** Each sentence must *mean* its frozen capability for **arbitrary**
   `Ω`. Two decisions make the adapters unconditional: the sentences talk about the
   *frozen* `seqCode` coding (a coding translation would need `Ω` closed under it,
   smuggling an ideal premise into statement adequacy), and the coding's operations are
   arithmetized by Gödel-β-coded runs — over standard ℕ only truth matters, not
   hierarchy position, so unbounded quantifiers are free.
4. **The payoffs.** Adapter + context realization + the frozen Kleene tree give the
   checked ω-model countermodel (`rca0_not_semantically_implies_wkl`); a Henkin-safe
   calculus, sound for *every* `Struc₂`, turns it into calculus-relative
   nonderivability (`rca0_not_derives_wkl`).
5. **The contract.** Typed export records carry the epistemic scope in their types;
   audit gates check each record reaches its named theorem and nothing it must not.

In one sentence: the bridge turns "the Kleene tree defeats WKL over REC" from a fact
about a Lean predicate into a checked model-theoretic and proof-theoretic statement
about formal RCA₀ — without moving a line of either frozen codebase.

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
- `rca0_not_derives_wkl`: `Rca0Theory ⊬ wklSentence` **in this calculus**; it never
  renders as an unqualified Simpson-style RCA₀ ⊬ WKL. No completeness claim is made
  anywhere.

**F3 (continued) — the pinned standard calculus `l2VarWitnessLK.v1`.**

- `StdLK` (`StandardCalculus.lean`): a bridge-defined, fully specified one-sided LK
  presentation of the conventional two-sorted logic *assumed* (not printed) in Simpson
  [Sim09] §I.2 — Foundation's pinned `Derivation` rule shape verbatim, except the
  second-order existential rule witnesses a **set variable** (the only set terms L₂
  has), never a formula: Foundation's formula-witness `exs₂` builds unrestricted
  comprehension into the logic and is deliberately excluded. The identification with
  Simpson's prose is a documented reading, never a checked claim.
- `StdLK.soundness` / `StdLKProvable.soundness`: **direct** soundness (no embedding
  into `Derivable`, no completeness). The theory-level form consumes
  `M.sets.Nonempty` — Simpson's nonempty-sort assumption as an explicit hypothesis.
  The deliberate contrast is checked: `stdLK_derives_exs₂_verum` proves `∃X ⊤`
  outright, which `Derivable` cannot (it is sound for empty designated parts).
- `rca0_not_stdLK_proves_wkl` (`StandardTurnstile.lean`):
  `Rca0Theory ⊬ wklSentence` **in `l2VarWitnessLK.v1`** — direct soundness at the REC
  structure (designated part nonempty) refuted through the Kleene tree. This
  discharges the previously recorded proof-system-adequacy debt by the direct-
  soundness route; the two calculi remain **independently** sound with no embedding
  claimed in either direction.

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
`henkinSafeV1`, comparison `recorded`; `NonderivabilityCertificate` — structurally
keyed to the calculus id; `SemanticCountermodelCertificate` — scope `allModels` over
general `Struc₂` structures, witnessed by an ω-structure; `StandardCalculusRecord` —
id `l2VarWitnessLKv1` with its `nonemptySetSort` assumption;
`CalculusComparisonCertificate` — relation `independentDirectSoundness`, deliberately
embedding-free; `StandardNonprovabilityCertificate` — keyed to the standard calculus
id). Downstream consumers cite these records and nothing else.

The reverse-mathlib **local certified facts** are unaffected by anything here —
adequacy evidence upgrades interpretation status, not another mathematical leaf. The
one exception is explicit and labeled: the validated semantic-countermodel record
contributes reverse-mathlib's backend-qualified all-model scoped result
(`all-model: 1 (backendChecked)`), the exact statement `Rca0Theory ⊭ wklSentence`
over all general L₂ structures — never an unqualified conventional-RCA₀ claim; and
the validated standard-calculus nonderivability record contributes the
backend-qualified syntactic scoped result (`syntactic: 1 (backendChecked)`), the
exact statement `Rca0Theory ⊬ wklSentence in l2VarWitnessLK.v1` — likewise never an
unqualified conventional-RCA₀ ⊬ WKL claim.

## Verification

- `lake build` — the full rollup, `warningAsError` on.
- `lake env lean scripts/Audit.lean` — axiom sweep (standard three only, every
  bridge-owned declaration including private/auxiliary) plus per-headline dependency
  gates: each gated theorem and export record must reach its named load-bearing
  dependencies, and no export leaf may reach the derived composition.

Both run in CI on every push.

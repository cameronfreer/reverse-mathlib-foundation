# reverse-mathlib-foundation

**Tranche F1: the isolated ω-semantics bridge** between two pinned projects —
[reverse-mathlib](https://github.com/cameronfreer/reverse-mathlib) (the Turing-ideal ω
layer, frozen) and [Foundation](https://github.com/FormalizedFormalLogic/Foundation)
(second-order Tarski semantics). Neither core repository depends on the other; this
workspace depends on both, at exact pinned revisions (see `lakefile.toml`), on
Foundation's toolchain. Narrow Foundation imports only — never `import Foundation`.

Semantic bridge only: no derivation calculus, no soundness (tranche F3), no upstream
action, no changes to either core. The reverse-mathlib scoreboard (ω-model: 3 /
all-model: 0 / syntactic: 0) is not affected by anything here — adequacy evidence
upgrades interpretation status, it is not another mathematical leaf.

## F1 state

- [x] Step 0 — pinned import-surface prototype: both projects compile in one workspace
      (reverse-mathlib `ff824c1` rebuilt under Lean v4.32.2 + mathlib v4.32.2-tag;
      Foundation `9800e78`).
- [x] Step 1 — `OmegaPart.toFoundation` with the standard arithmetic interpretation on ℕ
      supplied and verified explicitly (never manufactured implicitly); evaluation bridge
      lemmas; first cross-layer REC evaluation.
- [ ] Step 2 — the explicit semantic RCA₀^ω theory (restricted comprehension as explicit
      theory obligations, never hidden in logical substitution).
- [ ] Step 3 — both directional context-adequacy theorems, kept separate until exact:
      `IsTuringIdeal Ω → Ω.toFoundation ⊧* RCA₀^ω` (unlocks the REC countermodel reading)
      and the converse (unlocks universal positive ω-model readings).
- [ ] Step 4 — the exact binary-tree WKL statement adapter.
- [ ] Step 5 — the REC regression: `M_REC ⊧ RCA₀^ω` and `M_REC ⊭ ŴKL`.

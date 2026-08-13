/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import RMFoundationBridge.StandardCalculus
import RMFoundationBridge.Turnstile

/-!
# F3, fourth layer: the standard-calculus negative turnstile

Direct soundness of the pinned standard calculus (`l2VarWitnessLK.v1`) composed with the
semantic countermodel: the ŴKL sentence is not provable from `Rca0Theory` in the pinned
standard calculus. The witness structure is `recursivePart.toFoundation`; its designated
part is **nonempty** (the empty set is recursive), which is exactly the nonempty-sort
assumption the standard calculus's theory-level soundness consumes.

**Scope**: nonprovability in the bridge-defined pinned standard calculus
`l2VarWitnessLK.v1` — the fully specified LK presentation of the conventional two-sorted
logic assumed in Simpson [Sim09] §I.2 — from the semantic `Rca0Theory` axiom set, over
the canonical coding. **No completeness claim** anywhere: provability is not asserted to
exhaust semantic consequence. The result renders exactly as
`Rca0Theory ⊬ wklSentence` **in `l2VarWitnessLK.v1`**, never as an unqualified
Simpson-style RCA₀ ⊬ WKL: the identification of the pinned calculus with Simpson's
prose logic is a documented reading of §I.2, not a checked theorem.

This discharges the proof-system-adequacy debt recorded in `Turnstile.lean` by the route
that file names ("soundness proved directly for that pinned calculus"): the Henkin-safe
calculus and the pinned standard calculus are **independently** sound — the Henkin-safe
one over every designated part, the standard one over nonempty equality-correct
designated parts — and nothing here carries or licenses a derivability transfer
between them.
-/

namespace RMFoundationBridge

open LO LO.FirstOrder LO.SecondOrder
open ReverseMathlib.Omega

/-- The REC structure satisfies the nonempty-sort assumption of the standard calculus:
its designated part is nonempty (the empty set is recursive). -/
theorem recursivePart_toFoundation_sets_nonempty :
    (recursivePart.toFoundation).sets.Nonempty := by
  have h := recursivePart_toFoundation_models_exs₂_verum
  rw [models_def] at h
  obtain ⟨X, hX, -⟩ := h
  exact ⟨X, hX⟩

/-- The REC structure satisfies the equality-correctness assumption: the standard
interpretation reads the equality symbol as identity on ℕ (definitionally). -/
theorem recursivePart_toFoundation_eqCorrect :
    EqCorrect recursivePart.toFoundation := fun a b =>
  standardInterpretation_eq ![a, b]

/-- **The standard-calculus negative turnstile**: `Rca0Theory ⊬ ŴKL` in the pinned
standard calculus `l2VarWitnessLK.v1` — direct soundness instantiated at the REC
structure (whose designated part is nonempty and whose equality symbol means
identity), refuted by the Kleene tree through the unconditional adapter. -/
theorem rca0_not_stdLK_proves_wkl : ¬ StdLKProvable Rca0Theory wklSentence := fun h =>
  recursivePart_not_models_wklSentence
    (h.soundness recursivePart.toFoundation recursivePart_toFoundation_sets_nonempty
      recursivePart_toFoundation_eqCorrect
      fun _ hτ => recursivePart_models_rca0 hτ)

end RMFoundationBridge

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Omega.Equivalence
import ReverseMathlib.Omega.HallFromEfilc
import RMFoundationBridge.HallSentence
import RMFoundationBridge.WklRegression

/-!
# F2, fourth layer: semantic compositions over Turing ideals

The three unconditional statement adapters composed with the three **frozen**
certified transformations (`weakKonigAt_of_efilcAt`, `efilcAt_of_weakKonigAt`,
`countableHallAt_of_efilcAt` — each taking `IsTuringIdeal Ω`): sentence-level
implications between ŴKL, EFILC, and one-sided Hall at every Turing ideal, plus the
REC corollary for EFILC. **No new derivation claims** — everything here is semantic,
and the Turing-ideal premise enters only through the frozen transformations, never
through the adapters.

Registry discipline note: the WKL → Hall composition below is the **derived**
composition of the two certified transformations, matching the frozen zoo decision
that ŴKL → Hall stays derived-only — it is provided for convenience and is not a
third certified fact.
-/

namespace RMFoundationBridge

open LO LO.FirstOrder LO.SecondOrder
open ReverseMathlib.Omega

/-- **EFILC ↔ ŴKL at every Turing ideal**, at the sentence level: the two adapters
composed with the frozen interchange pair. -/
theorem models_efilcSentence_iff_wklSentence {Ω : OmegaPart} (h : IsTuringIdeal Ω) :
    Ω.toFoundation ⊧ efilcSentence ↔ Ω.toFoundation ⊧ wklSentence := by
  rw [models_efilcSentence_iff, models_wklSentence_iff]
  exact ⟨weakKonigAt_of_efilcAt h, efilcAt_of_weakKonigAt h⟩

/-- **EFILC → Hall at every Turing ideal**, at the sentence level: the adapters
composed with the frozen Hall-from-EFILC construction. -/
theorem models_hallSentence_of_models_efilcSentence {Ω : OmegaPart}
    (h : IsTuringIdeal Ω) :
    Ω.toFoundation ⊧ efilcSentence → Ω.toFoundation ⊧ hallSentence := by
  rw [models_efilcSentence_iff, models_hallSentence_iff]
  exact countableHallAt_of_efilcAt h

/-- ŴKL → Hall at every Turing ideal — the **derived** composition (not a third
certified fact; see the module docstring). -/
theorem models_hallSentence_of_models_wklSentence {Ω : OmegaPart}
    (h : IsTuringIdeal Ω) :
    Ω.toFoundation ⊧ wklSentence → Ω.toFoundation ⊧ hallSentence := fun hw =>
  models_hallSentence_of_models_efilcSentence h
    ((models_efilcSentence_iff_wklSentence h).mpr hw)

/-- The REC structure falsifies the EFILC sentence: the interchange at the recursive
Turing ideal transfers the Kleene-tree refutation. -/
theorem recursivePart_not_models_efilcSentence :
    ¬ recursivePart.toFoundation ⊧ efilcSentence := fun h =>
  recursivePart_not_models_wklSentence
    ((models_efilcSentence_iff_wklSentence recursivePart_isTuringIdeal).mp h)

/-- **The EFILC countermodel corollary**: the EFILC sentence is not a semantic
consequence of `Rca0Theory` over ω-structures. -/
theorem rca0_not_semantically_implies_efilc :
    ∃ M : Struc₂.{0, 0} ℒₒᵣ, (∀ σ ∈ Rca0Theory, M ⊧ σ) ∧ ¬ M ⊧ efilcSentence :=
  ⟨recursivePart.toFoundation, fun _ => recursivePart_models_rca0,
    recursivePart_not_models_efilcSentence⟩

end RMFoundationBridge

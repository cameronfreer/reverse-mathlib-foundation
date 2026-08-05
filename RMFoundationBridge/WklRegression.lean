/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import RMFoundationBridge.WklSentence
import RMFoundationBridge.ForwardAdequacy

/-!
# F1 step 5: the REC regression

The two halves of the F1 regression meet: the recursive-set second-order part satisfies
every axiom of semantic RCA₀ on ω-structures (`recursivePart_models_rca0`, context
adequacy at REC) yet does not satisfy the ŴKL sentence — the unconditional statement
adapter composed with the frozen Kleene-tree separation
(`not_weakKonigAt_recursivePart`). This is the ω-model reading of RCA₀ ⊬ WKL at the
semantic layer; the syntactic reading (a derivation calculus and soundness) is tranche
F3 and remains out of scope.
-/

namespace RMFoundationBridge

open LO LO.FirstOrder LO.SecondOrder
open ReverseMathlib.Omega

/-- **The REC countermodel, second half**: the recursive-set second-order part does not
satisfy the ŴKL sentence — the unconditional adapter composed with the frozen Kleene
tree. -/
theorem recursivePart_not_models_wklSentence :
    ¬ recursivePart.toFoundation ⊧ wklSentence := fun h =>
  not_weakKonigAt_recursivePart (models_wklSentence_iff.mp h)

/-- **The F1 regression, assembled**: one structure satisfies every semantic RCA₀ axiom
and falsifies the ŴKL sentence — so the ŴKL sentence is not a semantic consequence of
`Rca0Theory` over ω-structures. -/
theorem rca0_not_semantically_implies_wkl :
    ∃ M : Struc₂.{0, 0} ℒₒᵣ, (∀ σ ∈ Rca0Theory, M ⊧ σ) ∧ ¬ M ⊧ wklSentence :=
  ⟨recursivePart.toFoundation, fun _ => recursivePart_models_rca0,
    recursivePart_not_models_wklSentence⟩

end RMFoundationBridge

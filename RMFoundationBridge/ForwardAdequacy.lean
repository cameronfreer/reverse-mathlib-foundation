/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import RMFoundationBridge.Delta01Decide
import RMFoundationBridge.Satisfaction

/-!
# F1: comprehension internality and forward adequacy

The internality layer is where `IsTuringIdeal` finally enters — in exactly one place.
`comprehension_internal` packages the dovetailed decision through the finite-parameter
oracle's ideal membership and downward closure; `forward_adequacy` is then the
transparent case analysis promised by the dispatcher's type: every branch except
comprehension was closed for every `Ω` long ago, and the Turing-ideal hypothesis is
consumed in the single remaining branch.

**Forward context adequacy** (the direction whose payoff is the REC countermodel
reading): every Turing ideal satisfies every axiom of semantic RCA₀ on ω-structures.
Instantiated at REC. The converse direction, the statement adapters, the derivation
calculus, and any registry integration remain out of scope, per the standing boundary.
-/

namespace RMFoundationBridge

open LO LO.FirstOrder LO.SecondOrder
open ReverseMathlib.Omega

/-- **Comprehension internality**: in a Turing ideal containing the set parameters, the
set defined by a Δ⁰₁ pair belongs to the ideal — the dovetailed decision composed with
the finite-parameter oracle's membership and downward closure. `IsTuringIdeal` is
consumed here and nowhere else in forward adequacy. -/
theorem comprehension_internal {Ω : OmegaPart} (h : IsTuringIdeal Ω) {N k : ℕ}
    {φ ψ : SecondOrder.Semiformula ℒₒᵣ Empty Empty N (k + 1)}
    (hφ : IsSigma01 φ) (hψ : IsPi01 ψ) (𝕊 : Set (Set ℕ)) (E : Fin N → Set ℕ)
    (hE : ∀ i, E i ∈ Ω) (e : Fin k → ℕ)
    (heq : ∀ x : ℕ, EvalN 𝕊 φ E (x :> e) ↔ EvalN 𝕊 ψ E (x :> e)) :
    {x : ℕ | EvalN 𝕊 φ E (x :> e)} ∈ Ω :=
  h.mem_of_reducible (finiteParamOracle_mem h hE)
    (delta01_reducible E 𝕊 hφ hψ e heq)

/-- **Forward context adequacy**: every Turing ideal satisfies every axiom of semantic
RCA₀ on ω-structures. Transparent case analysis over the axiom origin — the basic axioms
and induction instances hold for every second-order part, and the Turing-ideal
hypothesis is consumed in exactly the comprehension branch. -/
theorem forward_adequacy {Ω : OmegaPart} (h : IsTuringIdeal Ω)
    {σ : SecondOrder.Sentence ℒₒᵣ} (hσ : σ ∈ Rca0Theory) :
    Ω.toFoundation ⊧ σ := by
  refine models_of_axiomOrigin hσ fun {N k} φ ψ hφ hψ => ?_
  rw [models_comprehensionInstance_iff]
  intro E hE e heq
  exact ⟨{x : ℕ | EvalN Ω.sets φ E (x :> e)},
    comprehension_internal h hφ hψ Ω.sets E hE e heq, fun x => Iff.rfl⟩

/-- **The REC instance**, first half of the F1 regression: the recursive-set Turing
ideal satisfies every axiom of semantic RCA₀ on ω-structures. (The second half —
`M_REC ⊭ ŴKL` — awaits the exact binary-tree WKL statement adapter, F1 step 4.) -/
theorem recursivePart_models_rca0 {σ : SecondOrder.Sentence ℒₒᵣ}
    (hσ : σ ∈ Rca0Theory) : recursivePart.toFoundation ⊧ σ :=
  forward_adequacy recursivePart_isTuringIdeal hσ

end RMFoundationBridge

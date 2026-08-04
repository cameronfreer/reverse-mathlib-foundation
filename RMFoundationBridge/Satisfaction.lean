/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import RMFoundationBridge.SchemaExpansion

/-!
# F1 item 4: standard-model satisfaction — everything except comprehension

The dependency split is preserved in the theorem types:

* every **basic arithmetic axiom** is satisfied by `Ω.toFoundation` for *every*
  `OmegaPart Ω` — no `IsTuringIdeal`;
* every **induction instance** likewise holds for every `Ω`: standard-number induction
  does the work, not ideal closure. The `IsSigma01` witness is **deliberately absent**
  from `models_inductionSentence`: standard ℕ satisfies induction for every externally
  definable predicate. The Σ⁰₁ restriction belongs to `AxiomOrigin`, which determines the
  object theory; the metatheoretic satisfaction argument is stronger — that gap is
  mathematically informative, not an omission;
* **Δ⁰₁ comprehension is deliberately not proved here**: the dispatcher
  `models_of_axiomOrigin` takes the comprehension branch as its sole hypothesis, so
  "comprehension is the only computational content of forward adequacy" is a structural
  fact about the theorem's type, and `IsTuringIdeal` will be consumed in exactly one
  branch when item 5 discharges it.

One small satisfaction theorem per named axiom keeps failures attributable, and each
proof runs through the explicitly supplied standard interpretation via the closure
evaluation theorem — never accidental instance search.

There is deliberately **no** `Ω.toFoundation ⊧* Rca0Theory` theorem in this module.
-/

namespace RMFoundationBridge

open LO LO.FirstOrder LO.SecondOrder
open ReverseMathlib.Omega

/-! ### The basic axioms, one satisfaction theorem each -/

theorem models_basicSuccNeZero (Ω : OmegaPart) : Ω.toFoundation ⊧ basicSuccNeZero := by
  rw [basicSuccNeZero, toFoundation_models_univClose_iff]
  intro E _ e
  change e 0 + 1 ≠ 0
  omega

theorem models_basicSuccInj (Ω : OmegaPart) : Ω.toFoundation ⊧ basicSuccInj := by
  rw [basicSuccInj, toFoundation_models_univClose_iff]
  intro E _ e
  change ¬(e 0 + 1 = e 1 + 1) ∨ e 0 = e 1
  omega

theorem models_basicAddZero (Ω : OmegaPart) : Ω.toFoundation ⊧ basicAddZero := by
  rw [basicAddZero, toFoundation_models_univClose_iff]
  intro E _ e
  change e 0 + 0 = e 0
  omega

theorem models_basicAddSucc (Ω : OmegaPart) : Ω.toFoundation ⊧ basicAddSucc := by
  rw [basicAddSucc, toFoundation_models_univClose_iff]
  intro E _ e
  change e 0 + (e 1 + 1) = (e 0 + e 1) + 1
  omega

theorem models_basicMulZero (Ω : OmegaPart) : Ω.toFoundation ⊧ basicMulZero := by
  rw [basicMulZero, toFoundation_models_univClose_iff]
  intro E _ e
  change e 0 * 0 = 0
  exact Nat.mul_zero (e 0)

theorem models_basicMulSucc (Ω : OmegaPart) : Ω.toFoundation ⊧ basicMulSucc := by
  rw [basicMulSucc, toFoundation_models_univClose_iff]
  intro E _ e
  change e 0 * (e 1 + 1) = (e 0 * e 1) + e 0
  exact Nat.mul_succ (e 0) (e 1)

theorem models_basicNotLtZero (Ω : OmegaPart) : Ω.toFoundation ⊧ basicNotLtZero := by
  rw [basicNotLtZero, toFoundation_models_univClose_iff]
  intro E _ e
  change ¬(e 0 < 0)
  omega

theorem models_basicLtSuccIff (Ω : OmegaPart) : Ω.toFoundation ⊧ basicLtSuccIff := by
  rw [basicLtSuccIff, toFoundation_models_univClose_iff]
  intro E _ e
  change (¬(e 0 < e 1 + 1) ∨ (e 0 < e 1 ∨ e 0 = e 1)) ∧
    ((¬(e 0 < e 1) ∧ ¬(e 0 = e 1)) ∨ e 0 < e 1 + 1)
  omega

/-! ### Induction instances, for every second-order part -/

/-- **Every** induction instance holds in **every** second-order part: standard-number
induction does the work. Note the `IsSigma01` witness is deliberately absent — standard ℕ
satisfies induction for every externally definable predicate; the Σ⁰₁ restriction belongs
to `AxiomOrigin` (the object theory), and this metatheoretic satisfaction argument is
strictly stronger. -/
theorem models_inductionSentence (Ω : OmegaPart) {N k : ℕ}
    (φ : SecondOrder.Semiformula ℒₒᵣ Empty Empty N (k + 1)) :
    Ω.toFoundation ⊧ inductionSentence φ := by
  rw [models_inductionInstance_iff]
  rintro E _ e ⟨hbase, hstep⟩ x
  induction x with
  | zero => exact hbase
  | succ n ih => exact hstep n ih

/-! ### The dispatcher -/

/-- **Origin dispatch, comprehension abstracted**: satisfaction of any axiom of
`Rca0Theory` by case analysis over its origin, with the Δ⁰₁-comprehension branch taken as
the sole hypothesis. Every other branch closes for every `Ω` with no Turing-ideal
assumption — so "Δ⁰₁ comprehension is the only computational content of forward adequacy"
is structural: item 5 supplies `hca` (consuming `IsTuringIdeal` in exactly that one
branch), and the final forward-adequacy theorem becomes transparent case analysis. -/
theorem models_of_axiomOrigin {Ω : OmegaPart} {σ : SecondOrder.Sentence ℒₒᵣ}
    (h : AxiomOrigin σ)
    (hca : ∀ {N k : ℕ} (φ ψ : SecondOrder.Semiformula ℒₒᵣ Empty Empty N (k + 1)),
      IsSigma01 φ → IsPi01 ψ → Ω.toFoundation ⊧ comprehensionSentence φ ψ) :
    Ω.toFoundation ⊧ σ := by
  cases h with
  | succNeZero => exact models_basicSuccNeZero Ω
  | succInj => exact models_basicSuccInj Ω
  | addZero => exact models_basicAddZero Ω
  | addSucc => exact models_basicAddSucc Ω
  | mulZero => exact models_basicMulZero Ω
  | mulSucc => exact models_basicMulSucc Ω
  | notLtZero => exact models_basicNotLtZero Ω
  | ltSuccIff => exact models_basicLtSuccIff Ω
  | sigma1Induction hφ => exact models_inductionSentence Ω _
  | delta1Comprehension hφ hψ => exact hca _ _ hφ hψ

end RMFoundationBridge

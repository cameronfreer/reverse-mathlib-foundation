/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import RMFoundationBridge.Basic

/-!
# F1 step 2 (first slice): the arithmetical formula class

The class on which the semantic RCA₀ schemas will be built: a second-order semiformula is
**arithmetical** when it contains no second-order quantifier. Number quantifiers and set
*parameters* — membership atoms against free or bound set variables — are allowed; `∀²`
and `∃²` are structurally excluded, so the Σ⁰₁/Π⁰₁/Δ⁰₁ classes defined over this
predicate are genuinely arithmetical-with-set-parameters, never Σ¹ₙ in disguise.

Presentation conventions are pinned in `Rca0Theory.lean` (Simpson [Sim09] §I.7–I.8 as the
claimed source). This module is pure syntax: the class and its closure lemmas. The
substitution-preservation lemmas land here (guardrail: before any schema depends on
them). Semantics-only tranche: no derivation calculus.
-/

namespace RMFoundationBridge

open LO LO.FirstOrder LO.SecondOrder

/-- No second-order quantifier occurs: the genuinely arithmetical (with set parameters)
semiformulas. -/
def IsArithmetical {L : Language} {Ξ ξ : Type*} :
    ∀ {N n : ℕ}, SecondOrder.Semiformula L Ξ ξ N n → Prop
  | _, _, .rel _ _ => True
  | _, _, .nrel _ _ => True
  | _, _, .bvar _ _ => True
  | _, _, .nbvar _ _ => True
  | _, _, .fvar _ _ => True
  | _, _, .nfvar _ _ => True
  | _, _, .verum => True
  | _, _, .falsum => True
  | _, _, .and φ ψ => IsArithmetical φ ∧ IsArithmetical ψ
  | _, _, .or φ ψ => IsArithmetical φ ∧ IsArithmetical ψ
  | _, _, .all₁ φ => IsArithmetical φ
  | _, _, .exs₁ φ => IsArithmetical φ
  | _, _, .all₂ _ => False
  | _, _, .exs₂ _ => False

namespace IsArithmetical

variable {L : Language} {Ξ ξ : Type*} {N n : ℕ}

@[simp] theorem rel {k : ℕ} (R : L.Rel k) (v : Fin k → Semiterm L ξ n) :
    IsArithmetical (Ξ := Ξ) (N := N) (.rel R v) := trivial

@[simp] theorem nrel {k : ℕ} (R : L.Rel k) (v : Fin k → Semiterm L ξ n) :
    IsArithmetical (Ξ := Ξ) (N := N) (.nrel R v) := trivial

@[simp] theorem and_iff {φ ψ : SecondOrder.Semiformula L Ξ ξ N n} :
    IsArithmetical (φ ⋏ ψ) ↔ IsArithmetical φ ∧ IsArithmetical ψ := Iff.rfl

@[simp] theorem or_iff {φ ψ : SecondOrder.Semiformula L Ξ ξ N n} :
    IsArithmetical (φ ⋎ ψ) ↔ IsArithmetical φ ∧ IsArithmetical ψ := Iff.rfl

@[simp] theorem all₁_iff {φ : SecondOrder.Semiformula L Ξ ξ N (n + 1)} :
    IsArithmetical (Semiformula.all₁ φ) ↔ IsArithmetical φ := Iff.rfl

@[simp] theorem exs₁_iff {φ : SecondOrder.Semiformula L Ξ ξ N (n + 1)} :
    IsArithmetical (Semiformula.exs₁ φ) ↔ IsArithmetical φ := Iff.rfl

@[simp] theorem not_all₂ {φ : SecondOrder.Semiformula L Ξ ξ (N + 1) n} :
    ¬ IsArithmetical (Semiformula.all₂ φ) := fun h => h

@[simp] theorem not_exs₂ {φ : SecondOrder.Semiformula L Ξ ξ (N + 1) n} :
    ¬ IsArithmetical (Semiformula.exs₂ φ) := fun h => h

/-- Negation preserves the arithmetical class (the syntax is negation-normal; `neg` swaps
duals without introducing quantifiers). -/
theorem neg {φ : SecondOrder.Semiformula L Ξ ξ N n} (h : IsArithmetical φ) :
    IsArithmetical (∼φ) := by
  induction φ with
  | and _ _ ihφ ihψ => exact ⟨ihφ h.1, ihψ h.2⟩
  | or _ _ ihφ ihψ => exact ⟨ihφ h.1, ihψ h.2⟩
  | all₁ _ ih => exact ih h
  | exs₁ _ ih => exact ih h
  | all₂ _ _ => exact h
  | exs₂ _ _ => exact h
  | _ => trivial

@[simp] theorem neg_iff {φ : SecondOrder.Semiformula L Ξ ξ N n} :
    IsArithmetical (∼φ) ↔ IsArithmetical φ := by
  constructor
  · intro h
    have h2 := h.neg
    rwa [SecondOrder.Semiformula.neg_neg] at h2
  · exact IsArithmetical.neg

/-- Material implication (`∼φ ⋎ ψ`, the arrow of the negation-normal syntax) preserves the
arithmetical class. -/
theorem imp {φ ψ : SecondOrder.Semiformula L Ξ ξ N n}
    (hφ : IsArithmetical φ) (hψ : IsArithmetical ψ) : IsArithmetical (∼φ ⋎ ψ) :=
  ⟨hφ.neg, hψ⟩

end IsArithmetical

end RMFoundationBridge

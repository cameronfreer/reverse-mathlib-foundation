/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import RMFoundationBridge.Basic

/-!
# F1 step 2 (first slice): the arithmetical formula class

**An inductive predicate**: a derivation of `IsArithmetical φ` exists exactly when `φ`
contains no second-order quantifier — there is deliberately no `all₂`/`exs₂` constructor,
so the refutations are inversion arguments and every preservation theorem is induction on
the derivation. Number quantifiers and set *parameters* (membership atoms against free or
bound set variables) are allowed, so the Σ⁰₁/Π⁰₁/Δ⁰₁ classes built on this predicate are
genuinely arithmetical-with-set-parameters, never Σ¹ₙ in disguise.

The predicate is not overloaded with computation: if a Boolean checker or a structural
characterization is needed later, it lands as a separate theorem, never by changing the
derivation system. Simp surface: constructor-shaped facts and refutations, single
direction only. Presentation conventions are pinned in `Rca0Theory.lean` (Simpson [Sim09]
§I.7–I.8 as the claimed source). Semantics-only tranche: no derivation calculus.
-/

namespace RMFoundationBridge

open LO LO.FirstOrder LO.SecondOrder

/-- No second-order quantifier occurs: derivations exist only for logical constants,
atomic formulas, set-membership atoms, propositional connectives, and first-order
quantifiers. -/
inductive IsArithmetical {L : Language} {Ξ ξ : Type*} :
    ∀ {N n : ℕ}, SecondOrder.Semiformula L Ξ ξ N n → Prop
  | rel {N n k : ℕ} (R : L.Rel k) (v : Fin k → Semiterm L ξ n) :
      IsArithmetical (N := N) (.rel R v)
  | nrel {N n k : ℕ} (R : L.Rel k) (v : Fin k → Semiterm L ξ n) :
      IsArithmetical (N := N) (.nrel R v)
  | bvar {N n : ℕ} (X : Fin N) (t : Semiterm L ξ n) : IsArithmetical (.bvar X t)
  | nbvar {N n : ℕ} (X : Fin N) (t : Semiterm L ξ n) : IsArithmetical (.nbvar X t)
  | fvar {N n : ℕ} (X : Ξ) (t : Semiterm L ξ n) : IsArithmetical (N := N) (.fvar X t)
  | nfvar {N n : ℕ} (X : Ξ) (t : Semiterm L ξ n) : IsArithmetical (N := N) (.nfvar X t)
  | verum {N n : ℕ} : IsArithmetical (N := N) (n := n) .verum
  | falsum {N n : ℕ} : IsArithmetical (N := N) (n := n) .falsum
  | and {N n : ℕ} {φ ψ : SecondOrder.Semiformula L Ξ ξ N n} :
      IsArithmetical φ → IsArithmetical ψ → IsArithmetical (φ ⋏ ψ)
  | or {N n : ℕ} {φ ψ : SecondOrder.Semiformula L Ξ ξ N n} :
      IsArithmetical φ → IsArithmetical ψ → IsArithmetical (φ ⋎ ψ)
  | all₁ {N n : ℕ} {φ : SecondOrder.Semiformula L Ξ ξ N (n + 1)} :
      IsArithmetical φ → IsArithmetical (.all₁ φ)
  | exs₁ {N n : ℕ} {φ : SecondOrder.Semiformula L Ξ ξ N (n + 1)} :
      IsArithmetical φ → IsArithmetical (.exs₁ φ)

namespace IsArithmetical

variable {L : Language} {Ξ ξ : Type*} {N n : ℕ}

/-! ### Refutations: no derivation reaches a second-order quantifier -/

@[simp] theorem not_all₂ {φ : SecondOrder.Semiformula L Ξ ξ (N + 1) n} :
    ¬ IsArithmetical (Semiformula.all₂ φ) := fun h => nomatch h

@[simp] theorem not_exs₂ {φ : SecondOrder.Semiformula L Ξ ξ (N + 1) n} :
    ¬ IsArithmetical (Semiformula.exs₂ φ) := fun h => nomatch h

/-! ### Inversion-backed simp surface (single direction only) -/

@[simp] theorem and_iff {φ ψ : SecondOrder.Semiformula L Ξ ξ N n} :
    IsArithmetical (φ ⋏ ψ) ↔ IsArithmetical φ ∧ IsArithmetical ψ :=
  ⟨fun h => by cases h with | and hφ hψ => exact ⟨hφ, hψ⟩, fun ⟨hφ, hψ⟩ => .and hφ hψ⟩

@[simp] theorem or_iff {φ ψ : SecondOrder.Semiformula L Ξ ξ N n} :
    IsArithmetical (φ ⋎ ψ) ↔ IsArithmetical φ ∧ IsArithmetical ψ :=
  ⟨fun h => by cases h with | or hφ hψ => exact ⟨hφ, hψ⟩, fun ⟨hφ, hψ⟩ => .or hφ hψ⟩

@[simp] theorem all₁_iff {φ : SecondOrder.Semiformula L Ξ ξ N (n + 1)} :
    IsArithmetical (Semiformula.all₁ φ) ↔ IsArithmetical φ :=
  ⟨fun h => by cases h with | all₁ hφ => exact hφ, .all₁⟩

@[simp] theorem exs₁_iff {φ : SecondOrder.Semiformula L Ξ ξ N (n + 1)} :
    IsArithmetical (Semiformula.exs₁ φ) ↔ IsArithmetical φ :=
  ⟨fun h => by cases h with | exs₁ hφ => exact hφ, .exs₁⟩

/-! ### Derivation transformations -/

/-- Negation is an ordinary derivation transformation: the syntax is negation-normal, so
`neg` swaps duals without touching the quantifier structure. -/
theorem neg {φ : SecondOrder.Semiformula L Ξ ξ N n} (h : IsArithmetical φ) :
    IsArithmetical (∼φ) := by
  induction h with
  | rel R v => exact .nrel R v
  | nrel R v => exact .rel R v
  | bvar X t => exact .nbvar X t
  | nbvar X t => exact .bvar X t
  | fvar X t => exact .nfvar X t
  | nfvar X t => exact .fvar X t
  | verum => exact .falsum
  | falsum => exact .verum
  | and _ _ ihφ ihψ => exact .or ihφ ihψ
  | or _ _ ihφ ihψ => exact .and ihφ ihψ
  | all₁ _ ih => exact .exs₁ ih
  | exs₁ _ ih => exact .all₁ ih

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
  .or hφ.neg hψ

end IsArithmetical

end RMFoundationBridge

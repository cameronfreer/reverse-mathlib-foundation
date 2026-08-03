/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Foundation.SecondOrder.Semantics
import Foundation.FirstOrder.Arithmetic.Basic.Model
import ReverseMathlib.Omega.KleeneTree

/-!
# Tranche F1, step 1: `OmegaPart.toFoundation` and the explicit standard interpretation

The isolated ω-semantics bridge between two pinned projects: reverse-mathlib's Turing-ideal
layer (`OmegaPart`, frozen) and Foundation's second-order semantics (`Struc₂`). Narrow
imports only — never `import Foundation`; neither core repository depends on the other.

Design obligations discharged here:

* the **standard arithmetic interpretation on ℕ is supplied and verified explicitly**
  (`standardInterpretation` plus the six symbol-verification lemmas) — `toFoundation`
  never manufactures it implicitly through instance search;
* `OmegaPart.toFoundation` is definitionally transparent: number sort standard ℕ, set sort
  exactly `Ω.sets` (`toFoundation_sets`, `toFoundation_Dom`);
* evaluation is bridged by `toFoundation_models_iff`, and the first genuine cross-layer
  evaluations (`toFoundation_models_exs₂_verum_iff`, with the REC instance
  `recursivePart_toFoundation_models_exs₂_verum`) confirm Foundation can evaluate
  sentences against reverse-mathlib's second-order parts.

Everything here is semantic. No derivation system is touched (that is tranche F3), and
nothing in the frozen Omega layer changes.
-/

namespace RMFoundationBridge

open LO LO.FirstOrder LO.SecondOrder
open ReverseMathlib.Omega

/-! ### The standard arithmetic interpretation, explicit and verified -/

/-- The standard interpretation of the arithmetic language `ℒₒᵣ` on `ℕ`: Foundation's
`standardModel`, bound to a bridge-owned name so the bridge supplies it explicitly rather
than through ambient instance search. -/
abbrev standardInterpretation : Structure ℒₒᵣ ℕ := Arithmetic.standardModel ℕ

/-- Verification: `0` means zero. -/
theorem standardInterpretation_zero (v : Fin 0 → ℕ) :
    standardInterpretation.func Language.ORing.Func.zero v = 0 := rfl

/-- Verification: `1` means one. -/
theorem standardInterpretation_one (v : Fin 0 → ℕ) :
    standardInterpretation.func Language.ORing.Func.one v = 1 := rfl

/-- Verification: `+` means addition on `ℕ`. -/
theorem standardInterpretation_add (v : Fin 2 → ℕ) :
    standardInterpretation.func Language.ORing.Func.add v = v 0 + v 1 := rfl

/-- Verification: `*` means multiplication on `ℕ`. -/
theorem standardInterpretation_mul (v : Fin 2 → ℕ) :
    standardInterpretation.func Language.ORing.Func.mul v = v 0 * v 1 := rfl

/-- Verification: `=` means equality on `ℕ`. -/
theorem standardInterpretation_eq (v : Fin 2 → ℕ) :
    standardInterpretation.rel Language.ORing.Rel.eq v ↔ v 0 = v 1 := Iff.rfl

/-- Verification: `<` means the order on `ℕ`. -/
theorem standardInterpretation_lt (v : Fin 2 → ℕ) :
    standardInterpretation.rel Language.ORing.Rel.lt v ↔ v 0 < v 1 := Iff.rfl

/-! ### The bridge constructor -/

/-- A second-order part as a Foundation second-order arithmetic structure: number sort
standard `ℕ` under the explicitly supplied `standardInterpretation`, set sort exactly
`Ω.sets`. -/
def _root_.ReverseMathlib.Omega.OmegaPart.toFoundation (Ω : OmegaPart) : Struc₂ ℒₒᵣ :=
  letI : Structure ℒₒᵣ ℕ := standardInterpretation
  Struc₂.of Ω.sets ℒₒᵣ

@[simp] theorem toFoundation_sets (Ω : OmegaPart) : Ω.toFoundation.sets = Ω.sets := rfl

@[simp] theorem toFoundation_Dom (Ω : OmegaPart) : Ω.toFoundation.Dom = ℕ := rfl

/-! ### Evaluation bridge -/

/-- Satisfaction in `Ω.toFoundation` is Tarski evaluation with set quantifiers ranging over
exactly `Ω.sets`. -/
theorem toFoundation_models_iff {Ω : OmegaPart} {σ : SecondOrder.Sentence ℒₒᵣ} :
    Ω.toFoundation ⊧ σ ↔
      letI : Structure ℒₒᵣ ℕ := standardInterpretation
      σ.Eval Ω.sets Empty.elim Empty.elim ![] ![] :=
  Iff.rfl

/-- First cross-layer evaluation: `∃² ⊤` holds in `Ω.toFoundation` iff the second-order
part is nonempty — the smallest sentence whose truth genuinely consults `Ω`. -/
theorem toFoundation_models_exs₂_verum_iff (Ω : OmegaPart) :
    Ω.toFoundation ⊧ (∃² ⊤ : SecondOrder.Sentence ℒₒᵣ) ↔ Ω.sets.Nonempty := by
  rw [toFoundation_models_iff]
  constructor
  · rintro ⟨X, hX, -⟩
    exact ⟨X, hX⟩
  · rintro ⟨X, hX⟩
    exact ⟨X, hX, trivial⟩

/-- The REC regression, first slice: Foundation evaluates the recursive-set second-order
part and sees a nonempty set sort (the empty set is recursive). -/
theorem recursivePart_toFoundation_models_exs₂_verum :
    recursivePart.toFoundation ⊧ (∃² ⊤ : SecondOrder.Sentence ℒₒᵣ) :=
  (toFoundation_models_exs₂_verum_iff recursivePart).mpr ⟨∅, recursiveSet_empty⟩

end RMFoundationBridge

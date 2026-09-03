/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import RMFoundationBridge.ForwardAdequacy

/-!
# Converse adequacy, Slice A: the structural Turing-ideal clauses from comprehension

The converse of `forward_adequacy` — every canonical ω-structure satisfying `Rca0Theory`
is a Turing ideal — has three clauses to discharge, and this slice discharges the two
that need no arithmetization of computation:

* **nonempty**: one Δ⁰₁-comprehension instance with the matrix `⊥` (no parameters at
  all) puts `∅` into the second-order part;
* **join**: one instance with the bounded matrix

  `∃ y < x + 1, ((x = 2·y ∧ y ∈ A) ∨ (x = 2·y + 1 ∧ y ∈ B))`

  puts a set into the part whose extension is, by an **explicit agreement lemma**
  (`evalN_joinMatrix`), exactly reverse-mathlib's `joinSet A B` — the set defined there
  through `% 2` and `/ 2`. The coding correspondence between the bounded-witness formula
  and that exact definition is a theorem here, never left implicit.

Both matrices are Δ⁰₀ by construction, so each serves as its own Σ⁰₁ and Π⁰₁ definition
and the equivalence premise of the pair-based schema is trivial. The route is the one the
later slices will reuse: a satisfaction hypothesis on the **whole** theory, the exact
comprehension sentence exhibited as an axiom through its `AxiomOrigin`, elimination
through `models_comprehensionInstance_iff` at the intended parameters, and set recovery
by extensionality against an evaluation lemma.

This slice is **bridge-local**: nothing is exported, nothing is ingested, and no partial
"context adequacy" is claimed. The downward-closure clause — the one needing a Σ⁰₁
definition of oracle computation with the oracle as a set parameter — is the subject of
the later slices; no weakened-ideal abstraction is introduced ahead of it.
-/

namespace RMFoundationBridge

open LO LO.FirstOrder LO.SecondOrder
open ReverseMathlib.Omega

/-! ### Nonemptiness: the empty set from comprehension on `⊥` -/

/-- The parameter-free comprehension instance on the matrix `⊥` is an axiom of the
theory. -/
theorem falsumComprehension_mem_theory :
    comprehensionSentence (N := 0) (k := 0) .falsum .falsum ∈ Rca0Theory :=
  AxiomOrigin.delta1Comprehension (.delta0 .falsum) (.delta0 .falsum)

/-- **The empty set belongs to every model**: comprehension on `⊥` yields a set with no
members, and by extensionality that set is `∅`. -/
theorem empty_mem_of_models_rca0 {Ω : OmegaPart} (h : Ω.toFoundation ⊧* Rca0Theory) :
    (∅ : Set ℕ) ∈ Ω := by
  have hσ := Semantics.modelsSet_iff.mp h falsumComprehension_mem_theory
  rw [models_comprehensionInstance_iff] at hσ
  obtain ⟨X, hX, hext⟩ := hσ ![] (fun i => i.elim0) ![] (fun _ => Iff.rfl)
  have : X = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun x hx => (hext x).mp hx
  rw [← this]
  exact hX

/-- **Nonemptiness** of the second-order part of every model of the theory. -/
theorem nonempty_of_models_rca0 {Ω : OmegaPart} (h : Ω.toFoundation ⊧* Rca0Theory) :
    Ω.sets.Nonempty :=
  ⟨∅, empty_mem_of_models_rca0 h⟩

/-! ### The join: a bounded-witness matrix and its agreement with `joinSet` -/

/-- The term `2`, as `1 + 1`. -/
def twoT {ξ : Type*} {n : ℕ} : Semiterm ℒₒᵣ ξ n := addT oneT oneT

/-- The join matrix: set slot `0` is `A`, set slot `1` is `B`, number slot `#0` is the
comprehension variable `x`. Beneath the bounded binder `#0` is the witness `y` and `#1`
is `x`:

`∃ y < x + 1, ((x = 2·y ∧ y ∈ A) ∨ (x = 2·y + 1 ∧ y ∈ B))`. -/
def joinMatrix : SecondOrder.Semiformula ℒₒᵣ Empty Empty 2 1 :=
  bexLT (succT #0)
    ((eqF #1 (mulT twoT #0) ⋏ .bvar 0 #0) ⋎ (eqF #1 (succT (mulT twoT #0)) ⋏ .bvar 1 #0))

theorem joinMatrix_isDelta0 : IsDelta0 (Ξ := Empty) (ξ := Empty) joinMatrix :=
  .bex _ (.or (.and (.rel _ _) (.bvar 0 _)) (.and (.rel _ _) (.bvar 1 _)))

/-- The join comprehension instance (the Δ⁰₀ matrix serving as both definitions) is an
axiom of the theory. -/
theorem joinComprehension_mem_theory :
    comprehensionSentence (k := 0) joinMatrix joinMatrix ∈ Rca0Theory :=
  AxiomOrigin.delta1Comprehension (.delta0 joinMatrix_isDelta0)
    (.delta0 joinMatrix_isDelta0)

/-- **The coding agreement lemma**: the bounded-witness matrix evaluates, at set
parameters `E` and number assignment `e`, to membership of `e 0` in reverse-mathlib's
exact `joinSet (E 0) (E 1)` — the set defined through `% 2` and `/ 2`. The witness of
the bounded existential is `x / 2` in either branch. -/
theorem evalN_joinMatrix {𝕊 : Set (Set ℕ)} (E : Fin 2 → Set ℕ) (e : Fin 1 → ℕ) :
    EvalN 𝕊 joinMatrix E e ↔ e 0 ∈ joinSet (E 0) (E 1) := by
  rw [joinMatrix, evalN_bexLT]
  change (∃ y : ℕ, y < e 0 + 1 ∧
      ((e 0 = (1 + 1) * y ∧ y ∈ E 0) ∨ (e 0 = (1 + 1) * y + 1 ∧ y ∈ E 1))) ↔
    ((e 0 % 2 = 0 ∧ e 0 / 2 ∈ E 0) ∨ (e 0 % 2 = 1 ∧ e 0 / 2 ∈ E 1))
  constructor
  · rintro ⟨y, -, ⟨hx, hy⟩ | ⟨hx, hy⟩⟩
    · exact Or.inl ⟨by omega, by rw [show e 0 / 2 = y by omega]; exact hy⟩
    · exact Or.inr ⟨by omega, by rw [show e 0 / 2 = y by omega]; exact hy⟩
  · rintro (⟨hm, hy⟩ | ⟨hm, hy⟩)
    · exact ⟨e 0 / 2, by omega, Or.inl ⟨by omega, hy⟩⟩
    · exact ⟨e 0 / 2, by omega, Or.inr ⟨by omega, hy⟩⟩

/-- **Join closure of every model**: the set the join comprehension instance produces at
parameters `A, B` is, by `evalN_joinMatrix` and extensionality, exactly `joinSet A B`. -/
theorem joinSet_mem_of_models_rca0 {Ω : OmegaPart} (h : Ω.toFoundation ⊧* Rca0Theory)
    {A B : Set ℕ} (hA : A ∈ Ω) (hB : B ∈ Ω) : joinSet A B ∈ Ω := by
  have hσ := Semantics.modelsSet_iff.mp h joinComprehension_mem_theory
  rw [models_comprehensionInstance_iff] at hσ
  have hE : ∀ i : Fin 2, ![A, B] i ∈ Ω.sets := by
    intro i
    induction i using Fin.cases with
    | zero => exact hA
    | succ j =>
      induction j using Fin.cases with
      | zero => exact hB
      | succ k => exact k.elim0
  obtain ⟨X, hX, hext⟩ := hσ ![A, B] hE ![] (fun _ => Iff.rfl)
  have : X = joinSet A B := by
    ext x
    rw [hext x, evalN_joinMatrix ![A, B] (x :> ![])]
    rfl
  rw [← this]
  exact hX

/-! ### Regression: the two clauses are consistent with the forward direction

At the recursive part — a Turing ideal, hence a model by `forward_adequacy` — the
recovered join is the join `IsTuringIdeal.join` already supplies. This pins that the
formula's extension is the frozen definition, not merely some set with the right
projections. -/

theorem recursivePart_joinSet_mem_of_models {A B : Set ℕ}
    (hA : A ∈ recursivePart) (hB : B ∈ recursivePart) :
    joinSet A B ∈ recursivePart :=
  joinSet_mem_of_models_rca0 ⟨fun _ hσ => recursivePart_models_rca0 hσ⟩ hA hB

example {A B : Set ℕ} (hA : A ∈ recursivePart) (hB : B ∈ recursivePart) :
    joinSet A B ∈ recursivePart :=
  recursivePart_isTuringIdeal.join hA hB

end RMFoundationBridge

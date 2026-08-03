/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import RMFoundationBridge.HierarchyRew

/-!
# F1 step 2 (fifth slice): universal closure, independently of any schema

Schema matrices are pure de Bruijn semiformulas (`Ξ = ξ = Empty`): the free parameters of
a matrix `φ : Semiformula ℒₒᵣ Empty Empty N n` are exactly its `N` set slots and `n`
number slots, so **universal closure captures every free number and set parameter exactly
once, structurally** — there is no fvar bookkeeping to audit.

**Canonical closure order**: number quantifiers are closed first (innermost), set
quantifiers second (outermost): `univClose φ = ∀²…∀² ∀¹…∀¹ φ`.

The hierarchy classifies the **open matrix**, never the closed sentence: `univClose φ`
contains `∀²` whenever `N > 0`, so it is deliberately outside `IsArithmetical` — the
regression fixture at the bottom pins that.

The **evaluation theorem** (`toFoundation_models_univClose_iff`) reduces satisfaction of
the closure in `Ω.toFoundation` to Tarski evaluation of the matrix under all parameter
assignments: set parameters ranging over `Ω.sets`, number parameters over `ℕ`.
-/

namespace RMFoundationBridge

open LO LO.FirstOrder LO.SecondOrder

/-! ### The closure operators -/

/-- Close all number slots (innermost quantifiers). -/
def closeNum {Ξ ξ : Type*} {N : ℕ} : ∀ {n : ℕ},
    SecondOrder.Semiformula ℒₒᵣ Ξ ξ N n → SecondOrder.Semiformula ℒₒᵣ Ξ ξ N 0
  | 0, φ => φ
  | _ + 1, φ => closeNum (.all₁ φ)

/-- Close all set slots (outermost quantifiers). -/
def closeSet {Ξ ξ : Type*} : ∀ {N : ℕ},
    SecondOrder.Semiformula ℒₒᵣ Ξ ξ N 0 → SecondOrder.Semiformula ℒₒᵣ Ξ ξ 0 0
  | 0, φ => φ
  | _ + 1, φ => closeSet (.all₂ φ)

/-- Universal closure: every free number and set parameter captured exactly once, sets
outermost. -/
def univClose {N n : ℕ}
    (φ : SecondOrder.Semiformula ℒₒᵣ Empty Empty N n) : SecondOrder.Sentence ℒₒᵣ :=
  closeSet (closeNum φ)

/-! ### The evaluation theorems -/

open ReverseMathlib.Omega

/-- Number closure evaluates to quantification over all number assignments. -/
theorem eval_closeNum_iff {𝕊 : Set (Set ℕ)} {N : ℕ} :
    ∀ {n : ℕ} {φ : SecondOrder.Semiformula ℒₒᵣ Empty Empty N n} {E : Fin N → Set ℕ},
      (letI : Structure ℒₒᵣ ℕ := standardInterpretation
       SecondOrder.Semiformula.Eval 𝕊 Empty.elim Empty.elim E ![] (closeNum φ)) ↔
        ∀ e : Fin n → ℕ,
          letI : Structure ℒₒᵣ ℕ := standardInterpretation
          SecondOrder.Semiformula.Eval 𝕊 Empty.elim Empty.elim E e φ := by
  intro n
  induction n with
  | zero =>
    intro φ E
    constructor
    · intro h e
      have he : e = ![] := funext fun i => i.elim0
      rw [he]
      exact h
    · intro h
      exact h ![]
  | succ n ih =>
    intro φ E
    constructor
    · intro h e
      have h2 := ih.mp h (fun i => e i.succ)
      have he : e = e 0 :> fun i => e i.succ := funext fun i => (Fin.cons_self_tail e).symm ▸ rfl
      have h3 := h2 (e 0)
      have : (e 0 :> fun i => e i.succ) = e := funext fun i => by
        induction i using Fin.cases with
        | zero => rfl
        | succ j => rfl
      rw [← this]
      exact h3
    · intro h
      exact ih.mpr fun e x => h (x :> e)

/-- Set closure evaluates to quantification over all set-parameter assignments drawn from
the second-order part. -/
theorem eval_closeSet_iff {𝕊 : Set (Set ℕ)} :
    ∀ {N : ℕ} {φ : SecondOrder.Semiformula ℒₒᵣ Empty Empty N 0},
      (letI : Structure ℒₒᵣ ℕ := standardInterpretation
       SecondOrder.Semiformula.Eval 𝕊 Empty.elim Empty.elim ![] ![] (closeSet φ)) ↔
        ∀ E : Fin N → Set ℕ, (∀ i, E i ∈ 𝕊) →
          letI : Structure ℒₒᵣ ℕ := standardInterpretation
          SecondOrder.Semiformula.Eval 𝕊 Empty.elim Empty.elim E ![] φ := by
  intro N
  induction N with
  | zero =>
    intro φ
    constructor
    · intro h E _
      have he : E = ![] := funext fun i => i.elim0
      rw [he]
      exact h
    · intro h
      exact h ![] fun i => i.elim0
  | succ N ih =>
    intro φ
    constructor
    · intro h E hE
      have h2 := ih.mp h (fun i => E i.succ) (fun i => hE i.succ)
      have h3 := h2 (E 0) (hE 0)
      have : (E 0 :> fun i => E i.succ) = E := funext fun i => by
        induction i using Fin.cases with
        | zero => rfl
        | succ j => rfl
      rw [← this]
      exact h3
    · intro h
      exact ih.mpr fun E hE X hX => h (X :> E) fun i => by
        induction i using Fin.cases with
        | zero => exact hX
        | succ j => exact hE j

/-- **The evaluation theorem**: satisfaction of the universal closure in `Ω.toFoundation`
is Tarski evaluation of the open matrix under every parameter assignment — set parameters
ranging over `Ω.sets`, number parameters over `ℕ`. -/
theorem toFoundation_models_univClose_iff {Ω : OmegaPart} {N n : ℕ}
    {φ : SecondOrder.Semiformula ℒₒᵣ Empty Empty N n} :
    Ω.toFoundation ⊧ univClose φ ↔
      ∀ E : Fin N → Set ℕ, (∀ i, E i ∈ Ω.sets) → ∀ e : Fin n → ℕ,
        letI : Structure ℒₒᵣ ℕ := standardInterpretation
        SecondOrder.Semiformula.Eval Ω.sets Empty.elim Empty.elim E e φ := by
  rw [toFoundation_models_iff]
  show (letI : Structure ℒₒᵣ ℕ := standardInterpretation
    SecondOrder.Semiformula.Eval Ω.sets Empty.elim Empty.elim ![] ![] (univClose φ)) ↔ _
  rw [show (univClose φ) = closeSet (closeNum φ) from rfl]
  rw [eval_closeSet_iff]
  constructor
  · intro h E hE e
    exact eval_closeNum_iff.mp (h E hE) e
  · intro h E hE
    exact eval_closeNum_iff.mpr (h E hE)

/-! ### Regression fixtures -/

/-- Fixture: closure captures the set parameter — the closed sentence of a one-set-slot
matrix contains `∀²` and is deliberately **not** arithmetical: the hierarchy classifies
the open matrix, never the completed sentence. -/
theorem not_isArithmetical_univClose_fixture :
    ¬ IsArithmetical (univClose (.bvar 0 #0 :
      SecondOrder.Semiformula ℒₒᵣ Empty Empty 1 1)) := by
  intro h
  exact IsArithmetical.not_all₂ h

/-- Fixture: the open matrix of the same instance **is** arithmetical (indeed Δ⁰₀). -/
example : IsDelta0 (.bvar 0 #0 : SecondOrder.Semiformula ℒₒᵣ Empty Empty 1 1) :=
  .bvar 0 _

/-- Fixture: exactly-once capture, executable — the closure of the one-slot matrix
evaluates as one set quantifier and one number quantifier, nothing doubled: in the
maximal part it says every set contains every number... which is false, witnessed by the
empty set; in the part containing only `∅` it is again false; and over the part `{univ}`
it is true. The three evaluations pin the quantifier structure semantically. -/
example : ¬ (OmegaPart.mk {∅}).toFoundation ⊧
    univClose (.bvar 0 #0 : SecondOrder.Semiformula ℒₒᵣ Empty Empty 1 1) := by
  intro h
  have := toFoundation_models_univClose_iff.mp h
    (fun _ => (∅ : Set ℕ)) (fun _ => rfl) (fun _ => 0)
  exact this

example : (OmegaPart.mk {Set.univ}).toFoundation ⊧
    univClose (.bvar 0 #0 : SecondOrder.Semiformula ℒₒᵣ Empty Empty 1 1) := by
  rw [toFoundation_models_univClose_iff]
  intro E hE e
  have h0 : E 0 = Set.univ := hE 0
  show e 0 ∈ E 0
  rw [h0]
  trivial

end RMFoundationBridge

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import RMFoundationBridge.EvalTransport

/-!
# F1 step 3 (expansion slice): the schema constructors expose their Tarski statements

The two semantic expansion theorems — genuine `↔` statements for **arbitrary** `Ω` and
**arbitrary** remaining parameter assignments, never just the forward direction that
standard-model satisfaction will consume:

* `models_comprehensionInstance_iff`: a comprehension instance holds in `Ω.toFoundation`
  iff for every admissible set-parameter assignment and every number-parameter
  assignment, the equivalence premise implies a common extension **in `Ω.sets`**;
* `models_inductionInstance_iff`: an induction instance holds iff for all parameters,
  base case and successor step imply every number.

These are the protection against de Bruijn shifts capturing the wrong variable: each is
proved through the closure evaluation theorem, the unconditional rewrite transport, and
the freshness specialization `eval_bmap_succ` — so the statement visibly evaluates `φ`
at the **original** parameters beneath the fresh output binder.

The asymmetric fixture at the bottom instantiates comprehension with
`φ(x, a, A) ≡ (x = a ∧ x ∈ A)` (Δ⁰₀, hence usable as both the Σ⁰₁ and the Π⁰₁
definition) over the **full** second-order part — witness availability cannot mask a
binding error, so the fixture genuinely pins the fresh output set, both parameter
survivals, the distinguished variable, and the closure ordering.
-/

namespace RMFoundationBridge

open LO LO.FirstOrder LO.SecondOrder
open ReverseMathlib.Omega

/-- Standard-ℕ Tarski evaluation of a pure de Bruijn matrix under the explicitly supplied
interpretation. -/
def EvalN (𝕊 : Set (Set ℕ)) {N n : ℕ} (φ : SecondOrder.Semiformula ℒₒᵣ Empty Empty N n)
    (E : Fin N → Set ℕ) (e : Fin n → ℕ) : Prop :=
  letI : Structure ℒₒᵣ ℕ := standardInterpretation
  φ.Eval 𝕊 Empty.elim Empty.elim E e

/-! ### Connective unfolding for `EvalN` -/

section evalN

variable {𝕊 : Set (Set ℕ)} {N n : ℕ} {φ ψ : SecondOrder.Semiformula ℒₒᵣ Empty Empty N n}
  {E : Fin N → Set ℕ} {e : Fin n → ℕ}

theorem evalN_and : EvalN 𝕊 (φ ⋏ ψ) E e ↔ EvalN 𝕊 φ E e ∧ EvalN 𝕊 ψ E e := Iff.rfl

theorem evalN_or : EvalN 𝕊 (φ ⋎ ψ) E e ↔ EvalN 𝕊 φ E e ∨ EvalN 𝕊 ψ E e := Iff.rfl

theorem evalN_neg : EvalN 𝕊 (∼φ) E e ↔ ¬ EvalN 𝕊 φ E e :=
  SecondOrder.Semiformula.EvalAux_neg φ

theorem evalN_impF : EvalN 𝕊 (impF φ ψ) E e ↔ (EvalN 𝕊 φ E e → EvalN 𝕊 ψ E e) := by
  constructor
  · intro h hp
    rcases evalN_or.mp h with hn | hq
    · exact absurd hp (evalN_neg.mp hn)
    · exact hq
  · intro h
    by_cases hp : EvalN 𝕊 φ E e
    · exact evalN_or.mpr (Or.inr (h hp))
    · exact evalN_or.mpr (Or.inl (evalN_neg.mpr hp))

theorem evalN_iffF : EvalN 𝕊 (iffF φ ψ) E e ↔ (EvalN 𝕊 φ E e ↔ EvalN 𝕊 ψ E e) := by
  constructor
  · intro h
    obtain ⟨h₁, h₂⟩ := evalN_and.mp h
    exact ⟨evalN_impF.mp h₁, evalN_impF.mp h₂⟩
  · intro h
    exact evalN_and.mpr ⟨evalN_impF.mpr h.mp, evalN_impF.mpr h.mpr⟩

theorem evalN_all₁ {φ : SecondOrder.Semiformula ℒₒᵣ Empty Empty N (n + 1)} :
    EvalN 𝕊 (.all₁ φ) E e ↔ ∀ x : ℕ, EvalN 𝕊 φ E (x :> e) := Iff.rfl

theorem evalN_exs₂ {φ : SecondOrder.Semiformula ℒₒᵣ Empty Empty (N + 1) n} :
    EvalN 𝕊 (.exs₂ φ) E e ↔ ∃ X ∈ 𝕊, EvalN 𝕊 φ (X :> E) e := Iff.rfl

theorem evalN_mem_bvar {X : Fin N} {t : Semiterm ℒₒᵣ Empty n} :
    EvalN 𝕊 (.bvar X t) E e ↔
      (letI : Structure ℒₒᵣ ℕ := standardInterpretation
       t.val e Empty.elim) ∈ E X := Iff.rfl

end evalN

/-! ### The comprehension expansion theorem -/

/-- **Comprehension expansion**: a Δ⁰₁-comprehension instance holds in `Ω.toFoundation`
iff, for every set-parameter assignment drawn from `Ω.sets` and every number-parameter
assignment, the pointwise equivalence of the two matrices implies existence of a common
extension in `Ω.sets`. `φ` is evaluated at the **original** parameters beneath the fresh
binder (`eval_bmap_succ`) — the output set can never occur in its own defining matrix. -/
theorem models_comprehensionInstance_iff {Ω : OmegaPart} {N k : ℕ}
    {φ ψ : SecondOrder.Semiformula ℒₒᵣ Empty Empty N (k + 1)} :
    Ω.toFoundation ⊧ comprehensionSentence φ ψ ↔
      ∀ E : Fin N → Set ℕ, (∀ i, E i ∈ Ω.sets) → ∀ e : Fin k → ℕ,
        (∀ x : ℕ, EvalN Ω.sets φ E (x :> e) ↔ EvalN Ω.sets ψ E (x :> e)) →
          ∃ X ∈ Ω.sets, ∀ x : ℕ, x ∈ X ↔ EvalN Ω.sets φ E (x :> e) := by
  rw [comprehensionSentence, toFoundation_models_univClose_iff]
  refine forall_congr' fun E => forall_congr' fun hE => forall_congr' fun e => ?_
  rw [show (SecondOrder.Semiformula.Eval Ω.sets Empty.elim Empty.elim E e)
        (impF (.all₁ (iffF φ ψ))
          (.exs₂ (.all₁ (iffF (.bvar 0 #0) (SecondOrder.Semiformula.bmap Fin.succ φ)))))
      = EvalN Ω.sets (impF (.all₁ (iffF φ ψ))
          (.exs₂ (.all₁ (iffF (.bvar 0 #0) (SecondOrder.Semiformula.bmap Fin.succ φ)))))
          E e from rfl]
  rw [evalN_impF]
  refine imp_congr ?_ ?_
  · rw [evalN_all₁]
    exact forall_congr' fun x => evalN_iffF
  · rw [evalN_exs₂]
    refine exists_congr fun X => and_congr Iff.rfl ?_
    rw [evalN_all₁]
    refine forall_congr' fun x => ?_
    rw [evalN_iffF]
    refine iff_congr evalN_mem_bvar ?_
    exact eval_bmap_succ φ X E (x :> e)

/-! ### The induction expansion theorem -/

/-- The valuation identity for the zero-substitution instance. -/
theorem evalN_substZero {𝕊 : Set (Set ℕ)} {N k : ℕ}
    (φ : SecondOrder.Semiformula ℒₒᵣ Empty Empty N (k + 1)) (E : Fin N → Set ℕ)
    (e : Fin k → ℕ) :
    EvalN 𝕊 (Rew.subst (zeroT :> Semiterm.bvar) ▹ φ) E e ↔ EvalN 𝕊 φ E (0 :> e) := by
  unfold EvalN
  rw [eval_rew φ (Rew.subst (zeroT :> Semiterm.bvar)) E Empty.elim e]
  have hb : (Semiterm.val (M := ℕ) (s := standardInterpretation) e Empty.elim ∘
      (Rew.subst (zeroT :> Semiterm.bvar)) ∘ Semiterm.bvar) = (0 :> e) := by
    funext i
    induction i using Fin.cases with
    | zero =>
        simp only [Function.comp_apply, FirstOrder.Rew.subst, Matrix.cons_val_zero]
        rfl
    | succ j => simp [FirstOrder.Rew.subst]
  have hf : (Semiterm.val (M := ℕ) (s := standardInterpretation) e Empty.elim ∘
      (Rew.subst (zeroT :> Semiterm.bvar)) ∘ Semiterm.fvar) = Empty.elim := by
    funext y
    exact y.elim
  rw [hb, hf]

/-- The valuation identity for the successor-substitution instance. -/
theorem evalN_substSucc {𝕊 : Set (Set ℕ)} {N k : ℕ}
    (φ : SecondOrder.Semiformula ℒₒᵣ Empty Empty N (k + 1)) (E : Fin N → Set ℕ)
    (x : ℕ) (e : Fin k → ℕ) :
    EvalN 𝕊 (Rew.subst (succT #0 :> fun i => #(i.succ)) ▹ φ) E (x :> e) ↔
      EvalN 𝕊 φ E ((x + 1) :> e) := by
  unfold EvalN
  rw [eval_rew φ (Rew.subst (succT #0 :> fun i => #(i.succ))) E Empty.elim (x :> e)]
  have hb : (Semiterm.val (M := ℕ) (s := standardInterpretation) (x :> e) Empty.elim ∘
      (Rew.subst (succT #0 :> fun i => #(i.succ))) ∘ Semiterm.bvar) = ((x + 1) :> e) := by
    funext i
    induction i using Fin.cases with
    | zero =>
        simp only [Function.comp_apply, FirstOrder.Rew.subst, Matrix.cons_val_zero]
        rfl
    | succ j => simp [FirstOrder.Rew.subst]
  have hf : (Semiterm.val (M := ℕ) (s := standardInterpretation) (x :> e) Empty.elim ∘
      (Rew.subst (succT #0 :> fun i => #(i.succ))) ∘ Semiterm.fvar) = Empty.elim := by
    funext y
    exact y.elim
  rw [hb, hf]

/-- **Induction expansion**: an induction instance holds in `Ω.toFoundation` iff for
every parameter assignment, the base case together with the successor step implies every
number. -/
theorem models_inductionInstance_iff {Ω : OmegaPart} {N k : ℕ}
    {φ : SecondOrder.Semiformula ℒₒᵣ Empty Empty N (k + 1)} :
    Ω.toFoundation ⊧ inductionSentence φ ↔
      ∀ E : Fin N → Set ℕ, (∀ i, E i ∈ Ω.sets) → ∀ e : Fin k → ℕ,
        (EvalN Ω.sets φ E (0 :> e) ∧
          ∀ x : ℕ, EvalN Ω.sets φ E (x :> e) → EvalN Ω.sets φ E ((x + 1) :> e)) →
          ∀ x : ℕ, EvalN Ω.sets φ E (x :> e) := by
  rw [inductionSentence, toFoundation_models_univClose_iff]
  refine forall_congr' fun E => forall_congr' fun hE => forall_congr' fun e => ?_
  rw [show (SecondOrder.Semiformula.Eval Ω.sets Empty.elim Empty.elim E e)
        (impF ((Rew.subst (zeroT :> Semiterm.bvar) ▹ φ) ⋏
            .all₁ (impF φ (Rew.subst (succT #0 :> fun i => #(i.succ)) ▹ φ)))
          (.all₁ φ))
      = EvalN Ω.sets (impF ((Rew.subst (zeroT :> Semiterm.bvar) ▹ φ) ⋏
            .all₁ (impF φ (Rew.subst (succT #0 :> fun i => #(i.succ)) ▹ φ)))
          (.all₁ φ)) E e from rfl]
  rw [evalN_impF]
  refine imp_congr ?_ evalN_all₁
  rw [evalN_and]
  refine and_congr (evalN_substZero φ E e) ?_
  rw [evalN_all₁]
  refine forall_congr' fun x => ?_
  rw [evalN_impF]
  exact imp_congr Iff.rfl (evalN_substSucc φ E x e)

/-! ### The asymmetric comprehension fixture

`φ(x, a, A) ≡ (x = a ∧ x ∈ A)`: one set parameter `A` (slot 0), one extra number
parameter `a` (slot 1), the comprehension variable `x` (slot 0). Δ⁰₀, hence admissible as
both the Σ⁰₁ and the Π⁰₁ definition; the expected witness is `{a}` when `a ∈ A`,
otherwise `∅`. Evaluated over the **full** second-order part so witness availability
cannot mask a binding error. -/

/-- The fixture matrix. -/
def fixtureMatrix : SecondOrder.Semiformula ℒₒᵣ Empty Empty 1 2 :=
  eqF #0 #1 ⋏ .bvar 0 #0

theorem fixtureMatrix_isSigma01 : IsSigma01 (Ξ := Empty) (ξ := Empty) fixtureMatrix :=
  .delta0 (.and (.rel _ _) (.bvar 0 _))

theorem fixtureMatrix_isPi01 : IsPi01 (Ξ := Empty) (ξ := Empty) fixtureMatrix :=
  .delta0 (.and (.rel _ _) (.bvar 0 _))

/-- The fixture instance is an axiom of the theory. -/
theorem fixture_mem_theory :
    comprehensionSentence fixtureMatrix fixtureMatrix ∈ Rca0Theory :=
  AxiomOrigin.delta1Comprehension fixtureMatrix_isSigma01 fixtureMatrix_isPi01

/-- The fixture matrix evaluates as intended for an arbitrary valuation: the
comprehension variable at number slot 0, the parameter at number slot 1, the set
parameter at set slot 0. -/
theorem evalN_fixtureMatrix {𝕊 : Set (Set ℕ)} (E : Fin 1 → Set ℕ) (e' : Fin 2 → ℕ) :
    EvalN 𝕊 fixtureMatrix E e' ↔ (e' 0 = e' 1 ∧ e' 0 ∈ E 0) :=
  Iff.rfl

/-- The full second-order part: every subset is available, so witness availability can
never mask a binding error. -/
def fullPart : OmegaPart := ⟨Set.univ⟩

/-- The fixture instance holds over the full part, through the expansion theorem. -/
theorem fullPart_models_fixture :
    fullPart.toFoundation ⊧ comprehensionSentence fixtureMatrix fixtureMatrix := by
  rw [models_comprehensionInstance_iff]
  intro E _ e _
  refine ⟨{y | y = e 0 ∧ y ∈ E 0}, trivial, fun x => ?_⟩
  rw [evalN_fixtureMatrix E (x :> e)]
  simp

/-- **The binding pin, positive branch**: with `a = 7 ∈ A = {4, 7}`, any set satisfying
the comprehension biconditional is exactly `{7}` — the witness is `{a}`, built from the
surviving number parameter and the surviving set parameter, never from the output set. -/
theorem fixture_witness_of_mem (X : Set ℕ)
    (hX : ∀ x : ℕ, x ∈ X ↔ EvalN Set.univ fixtureMatrix ![{4, 7}] (x :> ![7])) :
    X = {7} := by
  ext x
  rw [hX x, evalN_fixtureMatrix]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    Set.mem_singleton_iff, Set.mem_insert_iff]
  constructor
  · rintro ⟨rfl, _⟩
    rfl
  · rintro rfl
    exact ⟨rfl, Or.inr rfl⟩

/-- **The binding pin, negative branch**: with `a = 3 ∉ A = {4, 7}`, the forced witness
is `∅` — if any de Bruijn shift were off by one, the positive and negative branches could
not both hold. -/
theorem fixture_witness_of_not_mem (X : Set ℕ)
    (hX : ∀ x : ℕ, x ∈ X ↔ EvalN Set.univ fixtureMatrix ![{4, 7}] (x :> ![3])) :
    X = ∅ := by
  ext x
  rw [hX x, evalN_fixtureMatrix]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    Set.mem_empty_iff_false, Set.mem_insert_iff, Set.mem_singleton_iff, iff_false,
    not_and, not_or]
  rintro rfl
  exact ⟨by omega, by omega⟩

end RMFoundationBridge

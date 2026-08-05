/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import RMFoundationBridge.SchemaExpansion

/-!
# F3, first layer: a Henkin-safe derivation calculus with semantic soundness

**What this is not.** Foundation's second-order LK (`Foundation.SecondOrder.Derivation`)
has the formula-witness rule `exs₂ : ⊢ φ/⟦ψ⟧ :: Γ → ⊢ (∃² φ) :: Γ`, which builds
comprehension into the logic: it is sound for full semantics but **not** for an
arbitrary designated second-order part. That calculus is deliberately not used here.

**What this is.** A Hilbert-style calculus over open matrices
`SecondOrder.Semiformula ℒₒᵣ Empty Empty N n`, where the `N` open set slots and `n`
open number slots are read **universally** — set slots over the designated collection
`M.sets`, number slots over the domain (`SatOpen`). Under this reading:

* **second-order existential introduction is from an open set slot** (`exs₂I`): the
  premise is the matrix with its bound set variable identified with an existing open
  slot (`bmap (Fin.cases i id)`), so the witness is always a *variable* whose value
  lies in `M.sets` — never a formula;
* **comprehension is supplied only by theory axioms** (`axm` draws from `Γ`; no rule
  manufactures a set);
* generalization rules (`all₁I`, `all₂I`) need no freshness side conditions — a fresh
  slot *is* the universal reading;
* slot bookkeeping is exactly the two transport operations whose semantics are already
  proved unconditionally: number-variable rewriting (`rew`, via `eval_rew`) and
  set-slot renaming (`bmapR`, via `eval_bmap`).

**Soundness** (`soundness`, `soundness_sentence`) holds for **every** `Struc₂ ℒₒᵣ` —
arbitrary domain, arbitrary interpretation, arbitrary designated second-order part; all
arithmetic and all comprehension strength enter through `Γ` alone. **No completeness
claim is made anywhere.**
-/

namespace RMFoundationBridge

open LO LO.FirstOrder LO.SecondOrder

/-! ### Open-judgment satisfaction -/

/-- Satisfaction of an open matrix in a second-order structure: truth under **every**
assignment of the open set slots to designated sets and of the open number slots to
domain elements. At `N = n = 0` this is sentence satisfaction (`satOpen_sentence`). -/
def SatOpen (M : Struc₂ ℒₒᵣ) {N n : ℕ}
    (φ : SecondOrder.Semiformula ℒₒᵣ Empty Empty N n) : Prop :=
  ∀ E : Fin N → Set M.Dom, (∀ i, E i ∈ M.sets) → ∀ e : Fin n → M.Dom,
    φ.Eval M.sets Empty.elim Empty.elim E e

/-- At a sentence, open-judgment satisfaction is exactly `⊧`. -/
theorem satOpen_sentence {M : Struc₂ ℒₒᵣ} {σ : SecondOrder.Sentence ℒₒᵣ} :
    SatOpen M σ ↔ M ⊧ σ := by
  constructor
  · intro h
    exact models_def.mpr (h ![] (fun i => i.elim0) ![])
  · intro h E hE e
    have hE0 : E = ![] := funext fun i => i.elim0
    have he0 : e = ![] := funext fun i => i.elim0
    rw [hE0, he0]
    exact models_def.mp h

/-! ### General-structure evaluation helpers

The ℕ-specific transport lemmas of the adequacy layers have general-`M` counterparts;
these are the only three the soundness cases need beyond `eval_rew`/`eval_bmap`. -/

section evalHelpers

variable {M : Type*} [Structure ℒₒᵣ M] {𝕊 : Set (Set M)}

theorem eval_impF {N n : ℕ} {φ ψ : SecondOrder.Semiformula ℒₒᵣ Empty Empty N n}
    {E : Fin N → Set M} {e : Fin n → M} :
    (impF φ ψ).Eval 𝕊 Empty.elim Empty.elim E e ↔
      (φ.Eval 𝕊 Empty.elim Empty.elim E e → ψ.Eval 𝕊 Empty.elim Empty.elim E e) := by
  show (SecondOrder.Semiformula.EvalAux 𝕊 Empty.elim Empty.elim E e (∼φ) ∨
      SecondOrder.Semiformula.EvalAux 𝕊 Empty.elim Empty.elim E e ψ) ↔ _
  rw [SecondOrder.Semiformula.EvalAux_neg]
  exact Iff.symm (imp_iff_not_or)

/-- Substituting a term into the innermost number slot. -/
theorem eval_subst_cons {N n : ℕ}
    (φ : SecondOrder.Semiformula ℒₒᵣ Empty Empty N (n + 1))
    (t : Semiterm ℒₒᵣ Empty n) (E : Fin N → Set M) (e : Fin n → M) :
    ((Rew.subst (t :> Semiterm.bvar)) ▹ φ).Eval 𝕊 Empty.elim Empty.elim E e ↔
      φ.Eval 𝕊 Empty.elim Empty.elim E (t.val e Empty.elim :> e) := by
  rw [eval_rew φ (Rew.subst (t :> Semiterm.bvar)) E Empty.elim e]
  have hb : (Semiterm.val e Empty.elim ∘ (Rew.subst (t :> Semiterm.bvar)) ∘
      Semiterm.bvar) = (t.val e Empty.elim :> e) := by
    funext i
    induction i using Fin.cases with
    | zero => simp [FirstOrder.Rew.subst]
    | succ j => simp [FirstOrder.Rew.subst]
  have hf : (Semiterm.val e Empty.elim ∘ (Rew.subst (t :> Semiterm.bvar)) ∘
      Semiterm.fvar) = Empty.elim := by
    funext y
    exact y.elim
  rw [hb, hf]

/-- A shifted matrix does not see the innermost number slot. -/
theorem eval_bShiftF {N n : ℕ} (ψ : SecondOrder.Semiformula ℒₒᵣ Empty Empty N n)
    (E : Fin N → Set M) (x : M) (e : Fin n → M) :
    ((Rew.bShift : Rew ℒₒᵣ Empty n Empty (n + 1)) ▹ ψ).Eval 𝕊 Empty.elim Empty.elim E
        (x :> e) ↔
      ψ.Eval 𝕊 Empty.elim Empty.elim E e := by
  rw [eval_rew ψ Rew.bShift E Empty.elim (x :> e)]
  have hb : (Semiterm.val (x :> e) Empty.elim ∘ (Rew.bShift : Rew ℒₒᵣ Empty n Empty
      (n + 1)) ∘ Semiterm.bvar) = e := by
    funext i
    simp
  have hf : (Semiterm.val (x :> e) Empty.elim ∘ (Rew.bShift : Rew ℒₒᵣ Empty n Empty
      (n + 1)) ∘ Semiterm.fvar) = Empty.elim := by
    funext y
    exact y.elim
  rw [hb, hf]

end evalHelpers

/-! ### The calculus -/

/-- **The Henkin-safe calculus**: Hilbert-style derivability of open matrices from a
set of sentence axioms `Γ`. Second-order existential introduction is from an open set
slot only (`exs₂I`); no rule manufactures a set — comprehension can enter only through
`axm`. Every rule is sound for every `Struc₂ ℒₒᵣ` (`soundness`). -/
inductive Derivable (Γ : Set (SecondOrder.Sentence ℒₒᵣ)) :
    ∀ {N n : ℕ}, SecondOrder.Semiformula ℒₒᵣ Empty Empty N n → Prop
  -- axioms of the theory
  | axm {σ : SecondOrder.Sentence ℒₒᵣ} : σ ∈ Γ → Derivable Γ σ
  -- classical propositional base
  | verumI {N n : ℕ} : Derivable Γ (.verum : SecondOrder.Semiformula ℒₒᵣ Empty Empty N n)
  | falsumE {N n : ℕ} {φ : SecondOrder.Semiformula ℒₒᵣ Empty Empty N n} :
      Derivable Γ (.falsum : SecondOrder.Semiformula ℒₒᵣ Empty Empty N n) →
      Derivable Γ φ
  | andI {N n : ℕ} {φ ψ : SecondOrder.Semiformula ℒₒᵣ Empty Empty N n} :
      Derivable Γ φ → Derivable Γ ψ → Derivable Γ (φ ⋏ ψ)
  | andE₁ {N n : ℕ} {φ ψ : SecondOrder.Semiformula ℒₒᵣ Empty Empty N n} :
      Derivable Γ (φ ⋏ ψ) → Derivable Γ φ
  | andE₂ {N n : ℕ} {φ ψ : SecondOrder.Semiformula ℒₒᵣ Empty Empty N n} :
      Derivable Γ (φ ⋏ ψ) → Derivable Γ ψ
  | orI₁ {N n : ℕ} {φ ψ : SecondOrder.Semiformula ℒₒᵣ Empty Empty N n} :
      Derivable Γ φ → Derivable Γ (φ ⋎ ψ)
  | orI₂ {N n : ℕ} {φ ψ : SecondOrder.Semiformula ℒₒᵣ Empty Empty N n} :
      Derivable Γ ψ → Derivable Γ (φ ⋎ ψ)
  | orE {N n : ℕ} {φ ψ χ : SecondOrder.Semiformula ℒₒᵣ Empty Empty N n} :
      Derivable Γ (φ ⋎ ψ) → Derivable Γ (impF φ χ) → Derivable Γ (impF ψ χ) →
      Derivable Γ χ
  | axK {N n : ℕ} {φ ψ : SecondOrder.Semiformula ℒₒᵣ Empty Empty N n} :
      Derivable Γ (impF φ (impF ψ φ))
  | axS {N n : ℕ} {φ ψ χ : SecondOrder.Semiformula ℒₒᵣ Empty Empty N n} :
      Derivable Γ (impF (impF φ (impF ψ χ)) (impF (impF φ ψ) (impF φ χ)))
  | em {N n : ℕ} {φ : SecondOrder.Semiformula ℒₒᵣ Empty Empty N n} :
      Derivable Γ (φ ⋎ ∼φ)
  | mp {N n : ℕ} {φ ψ : SecondOrder.Semiformula ℒₒᵣ Empty Empty N n} :
      Derivable Γ (impF φ ψ) → Derivable Γ φ → Derivable Γ ψ
  -- slot bookkeeping: number-variable rewriting and set-slot renaming
  | rew {N n₁ n₂ : ℕ} (ω : Rew ℒₒᵣ Empty n₁ Empty n₂)
      {φ : SecondOrder.Semiformula ℒₒᵣ Empty Empty N n₁} :
      Derivable Γ φ → Derivable Γ (ω ▹ φ)
  | bmapR {N₁ N₂ n : ℕ} (g : Fin N₁ → Fin N₂)
      {φ : SecondOrder.Semiformula ℒₒᵣ Empty Empty N₁ n} :
      Derivable Γ φ → Derivable Γ (.bmap g φ)
  -- number quantifiers: an open slot is the universal reading
  | all₁I {N n : ℕ} {φ : SecondOrder.Semiformula ℒₒᵣ Empty Empty N (n + 1)} :
      Derivable Γ φ → Derivable Γ (.all₁ φ)
  | all₁E {N n : ℕ} {φ : SecondOrder.Semiformula ℒₒᵣ Empty Empty N (n + 1)} :
      Derivable Γ (.all₁ φ) → Derivable Γ φ
  | exs₁I {N n : ℕ} (t : Semiterm ℒₒᵣ Empty n)
      {φ : SecondOrder.Semiformula ℒₒᵣ Empty Empty N (n + 1)} :
      Derivable Γ ((Rew.subst (t :> Semiterm.bvar)) ▹ φ) → Derivable Γ (.exs₁ φ)
  | exs₁E {N n : ℕ} {φ : SecondOrder.Semiformula ℒₒᵣ Empty Empty N (n + 1)}
      {ψ : SecondOrder.Semiformula ℒₒᵣ Empty Empty N n} :
      Derivable Γ (.exs₁ φ) →
      Derivable Γ (impF φ ((Rew.bShift : Rew ℒₒᵣ Empty n Empty (n + 1)) ▹ ψ)) →
      Derivable Γ ψ
  -- set quantifiers: Henkin-safe — introduction from an open set slot only
  | all₂I {N n : ℕ} {φ : SecondOrder.Semiformula ℒₒᵣ Empty Empty (N + 1) n} :
      Derivable Γ φ → Derivable Γ (.all₂ φ)
  | all₂E {N n : ℕ} {φ : SecondOrder.Semiformula ℒₒᵣ Empty Empty (N + 1) n} :
      Derivable Γ (.all₂ φ) → Derivable Γ φ
  | exs₂I {N n : ℕ} (i : Fin N)
      {φ : SecondOrder.Semiformula ℒₒᵣ Empty Empty (N + 1) n} :
      Derivable Γ (.bmap (Fin.cases i id) φ) → Derivable Γ (.exs₂ φ)
  | exs₂E {N n : ℕ} {φ : SecondOrder.Semiformula ℒₒᵣ Empty Empty (N + 1) n}
      {ψ : SecondOrder.Semiformula ℒₒᵣ Empty Empty N n} :
      Derivable Γ (.exs₂ φ) → Derivable Γ (impF φ (.bmap Fin.succ ψ)) →
      Derivable Γ ψ

/-! ### Soundness -/

/-- **General semantic soundness**: every derivable open matrix is satisfied, under the
open-judgment reading, in **every** second-order structure satisfying the axioms —
arbitrary domain, arbitrary interpretation, arbitrary designated second-order part. -/
theorem soundness {Γ : Set (SecondOrder.Sentence ℒₒᵣ)} {N n : ℕ}
    {φ : SecondOrder.Semiformula ℒₒᵣ Empty Empty N n} (h : Derivable Γ φ)
    (M : Struc₂ ℒₒᵣ) (hΓ : ∀ τ ∈ Γ, M ⊧ τ) : SatOpen M φ := by
  induction h with
  | axm hσ =>
      exact satOpen_sentence.mpr (hΓ _ hσ)
  | verumI => exact fun E hE e => trivial
  | falsumE _ ih => exact fun E hE e => (ih E hE e).elim
  | andI _ _ ih₁ ih₂ => exact fun E hE e => ⟨ih₁ E hE e, ih₂ E hE e⟩
  | andE₁ _ ih => exact fun E hE e => (ih E hE e).1
  | andE₂ _ ih => exact fun E hE e => (ih E hE e).2
  | orI₁ _ ih => exact fun E hE e => Or.inl (ih E hE e)
  | orI₂ _ ih => exact fun E hE e => Or.inr (ih E hE e)
  | orE _ _ _ ih₁ ih₂ ih₃ =>
      intro E hE e
      rcases ih₁ E hE e with hl | hr
      · exact eval_impF.mp (ih₂ E hE e) hl
      · exact eval_impF.mp (ih₃ E hE e) hr
  | axK =>
      intro E hE e
      simp only [eval_impF]
      exact fun hφ _ => hφ
  | axS =>
      intro E hE e
      simp only [eval_impF]
      exact fun h₁ h₂ h₃ => h₁ h₃ (h₂ h₃)
  | @em N' n' φ' =>
      intro E hE e
      rcases Classical.em
        (SecondOrder.Semiformula.EvalAux M.sets Empty.elim Empty.elim E e φ') with
        h | h
      · exact Or.inl h
      · exact Or.inr ((SecondOrder.Semiformula.EvalAux_neg φ').mpr h)
  | mp _ _ ih₁ ih₂ =>
      exact fun E hE e => eval_impF.mp (ih₁ E hE e) (ih₂ E hE e)
  | rew ω _ ih =>
      intro E hE e
      rw [eval_rew _ ω E Empty.elim e]
      have hf : (Semiterm.val e Empty.elim ∘ ω ∘ Semiterm.fvar) = Empty.elim := by
        funext y
        exact y.elim
      rw [hf]
      exact ih E hE _
  | bmapR g _ ih =>
      intro E hE e
      rw [eval_bmap _ g E e]
      exact ih (E ∘ g) (fun i => hE (g i)) e
  | all₁I _ ih => exact fun E hE e x => ih E hE (x :> e)
  | all₁E _ ih =>
      intro E hE e
      have h := ih E hE (Matrix.vecTail e) (e 0)
      rwa [show (e 0 :> Matrix.vecTail e) = e from
        funext fun i => i.cases rfl fun j => rfl] at h
  | exs₁I t _ ih =>
      intro E hE e
      have h := ih E hE e
      rw [eval_subst_cons] at h
      exact ⟨_, h⟩
  | exs₁E _ _ ih₁ ih₂ =>
      intro E hE e
      obtain ⟨x, hx⟩ := ih₁ E hE e
      have h := eval_impF.mp (ih₂ E hE (x :> e)) hx
      rwa [eval_bShiftF] at h
  | all₂I _ ih =>
      exact fun E hE e X hX => ih (X :> E) (fun i => i.cases hX hE) e
  | all₂E _ ih =>
      intro E hE e
      have h := ih (E ∘ Fin.succ) (fun i => hE i.succ) e (E 0) (hE 0)
      rwa [show (E 0 :> (E ∘ Fin.succ)) = E from
        funext fun i => i.cases rfl fun j => rfl] at h
  | exs₂I i _ ih =>
      intro E hE e
      have h := ih E hE e
      rw [eval_bmap] at h
      refine ⟨E i, hE i, ?_⟩
      rwa [show (E ∘ Fin.cases i id) = (E i :> E) from
        funext fun j => j.cases rfl fun k => rfl] at h
  | exs₂E _ _ ih₁ ih₂ =>
      intro E hE e
      obtain ⟨X, hX, hφ⟩ := ih₁ E hE e
      have h := eval_impF.mp (ih₂ (X :> E) (fun i => i.cases hX hE) e) hφ
      rwa [eval_bmap_succ] at h

/-- **Soundness at sentences**, in the acceptance-boundary form:
`Derivable Γ σ → (∀ τ ∈ Γ, M ⊧ τ) → M ⊧ σ`, for every `M`. -/
theorem soundness_sentence {Γ : Set (SecondOrder.Sentence ℒₒᵣ)}
    {σ : SecondOrder.Sentence ℒₒᵣ} (h : Derivable Γ σ) (M : Struc₂ ℒₒᵣ)
    (hΓ : ∀ τ ∈ Γ, M ⊧ τ) : M ⊧ σ :=
  satOpen_sentence.mp (soundness h M hΓ)

end RMFoundationBridge

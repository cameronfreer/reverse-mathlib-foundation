/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import RMFoundationBridge.Rca0Theory

/-!
# F1 step 3 (transport slice): evaluation transport for rewriting

**Unconditional**: these theorems hold for arbitrary rewrites with no `IsArithmetical`
hypothesis — semantic substitution is unconditional; only preservation of the *syntactic
hierarchy* is restricted (`ArithmeticalRew`). Keeping the two facts separate is part of
the comprehension boundary: the restriction lives in the syntax classes, never in the
semantics.

* `eval_rew`: evaluating `ω ▹ φ` is evaluating `φ` under the transported number
  valuations (`Semiterm.val e f ∘ ω ∘ bvar/fvar`); set valuations are untouched.
* `eval_bmap`: evaluating `bmap g φ` is an explicit transformation of the **set
  valuation** — `φ` is evaluated at `E ∘ g`.
* `eval_bmap_succ` (the critical specialization): beneath a fresh output-set binder,
  `φ.bmap Fin.succ` makes `φ` see the **original** parameters `E`, never the new set at
  index zero.

The valuation algebra is factored into named lemmas (identity, composition,
bound-variable lift, cons/succ interaction) so the quantifier cases stay structural
rather than brittle simp chains.
-/

namespace RMFoundationBridge

open LO LO.FirstOrder LO.SecondOrder

variable {L : Language} {M : Type*} [𝓈 : Structure L M] {Ξ ξ ξ₁ ξ₂ : Type*}

/-! ### The valuation algebra, named -/

/-- Identity: rewriting by `Rew.id` does not move values. -/
theorem val_rew_id {n : ℕ} (t : Semiterm L ξ n) (e : Fin n → M) (f : ξ → M) :
    ((Rew.id : Rew L ξ n ξ n) t).val e f = t.val e f := by
  simp

/-- Composition: rewriting by a composite evaluates as sequential rewriting. -/
theorem val_rew_comp {n₁ n₂ n₃ : ℕ} {ξ₃ : Type*} (ω₂ : Rew L ξ₂ n₂ ξ₃ n₃)
    (ω₁ : Rew L ξ₁ n₁ ξ₂ n₂) (t : Semiterm L ξ₁ n₁) (e : Fin n₃ → M) (f : ξ₃ → M) :
    ((ω₂.comp ω₁) t).val e f = (ω₂ (ω₁ t)).val e f := by
  simp [Rew.comp_app]

/-- Bound-variable lift, fresh slot: the lifted rewrite maps the new variable to the new
value. -/
theorem val_q_zero {n₁ n₂ : ℕ} (ω : Rew L ξ₁ n₁ ξ₂ n₂) (x : M) (e : Fin n₂ → M)
    (f : ξ₂ → M) : (ω.q (#0 : Semiterm L ξ₁ (n₁ + 1))).val (x :> e) f = x := by
  simp

/-- Cons/succ interaction, bound side: the lifted rewrite on an old slot ignores the new
value. -/
theorem val_q_succ {n₁ n₂ : ℕ} (ω : Rew L ξ₁ n₁ ξ₂ n₂) (i : Fin n₁) (x : M)
    (e : Fin n₂ → M) (f : ξ₂ → M) :
    (ω.q (#(i.succ) : Semiterm L ξ₁ (n₁ + 1))).val (x :> e) f = (ω #i).val e f := by
  simp

/-- Cons/succ interaction, free side: the lifted rewrite on a free variable ignores the
new value. -/
theorem val_q_fvar {n₁ n₂ : ℕ} (ω : Rew L ξ₁ n₁ ξ₂ n₂) (y : ξ₁) (x : M)
    (e : Fin n₂ → M) (f : ξ₂ → M) :
    (ω.q (&y : Semiterm L ξ₁ (n₁ + 1))).val (x :> e) f = (ω &y).val e f := by
  simp

/-- Cons composed with the second-order retrusion: the fresh set stays at index zero, the
old sets route through `g`. -/
theorem cons_comp_retrusion {α : Type*} {N N' : ℕ} (X : α) (E : Fin N' → α)
    (g : Fin N → Fin N') : (X :> E) ∘ Fin.retrusion g = X :> (E ∘ g) := by
  funext i
  induction i using Fin.cases with
  | zero => simp [Fin.retrusion]
  | succ j => simp [Fin.retrusion]

/-! ### Evaluation transport for number-variable rewriting (arbitrary `Rew`) -/

/-- **Unconditional evaluation transport**: evaluating a rewritten formula is evaluating
the original under the transported number valuations; the set valuations `𝕊`, `F`, `E`
are untouched. No syntactic-class hypothesis appears — semantic substitution is
unconditional. -/
theorem eval_rew {𝕊 : Set (Set M)} {F : Ξ → Set M} :
    ∀ {N n₁ : ℕ} (φ : SecondOrder.Semiformula L Ξ ξ₁ N n₁) {n₂ : ℕ}
      (ω : Rew L ξ₁ n₁ ξ₂ n₂) (E : Fin N → Set M) (f : ξ₂ → M) (e : Fin n₂ → M),
      ((ω ▹ φ).Eval 𝕊 F f E e ↔
        φ.Eval 𝕊 F (Semiterm.val e f ∘ ω ∘ Semiterm.fvar) E
          (Semiterm.val e f ∘ ω ∘ Semiterm.bvar))
  | _, _, .rel R v, _, ω, E, f, e =>
      iff_of_eq (congrArg (𝓈.rel R) (funext fun i => Semiterm.val_rew ω (v i)))
  | _, _, .nrel R v, _, ω, E, f, e =>
      iff_of_eq (congrArg (¬ 𝓈.rel R ·)
        (funext fun i => Semiterm.val_rew ω (v i)))
  | _, _, .bvar X t, _, ω, E, f, e =>
      iff_of_eq (congrArg (· ∈ E X) (Semiterm.val_rew ω t))
  | _, _, .nbvar X t, _, ω, E, f, e =>
      iff_of_eq (congrArg (· ∉ E X) (Semiterm.val_rew ω t))
  | _, _, .fvar X t, _, ω, E, f, e =>
      iff_of_eq (congrArg (· ∈ F X) (Semiterm.val_rew ω t))
  | _, _, .nfvar X t, _, ω, E, f, e =>
      iff_of_eq (congrArg (· ∉ F X) (Semiterm.val_rew ω t))
  | _, _, .verum, _, ω, E, f, e => Iff.rfl
  | _, _, .falsum, _, ω, E, f, e => Iff.rfl
  | _, _, .and φ ψ, _, ω, E, f, e =>
      and_congr (eval_rew φ ω E f e) (eval_rew ψ ω E f e)
  | _, _, .or φ ψ, _, ω, E, f, e =>
      or_congr (eval_rew φ ω E f e) (eval_rew ψ ω E f e)
  | _, _, .all₁ φ, _, ω, E, f, e => by
      refine forall_congr' fun x => (eval_rew φ ω.q E f (x :> e)).trans ?_
      have hb : (Semiterm.val (x :> e) f ∘ ω.q ∘ Semiterm.bvar) =
          (x :> (Semiterm.val e f ∘ ω ∘ Semiterm.bvar)) := by
        funext i
        induction i using Fin.cases with
        | zero => simp [Function.comp_def]
        | succ j => simp [Function.comp_def]
      have hf : (Semiterm.val (x :> e) f ∘ ω.q ∘ Semiterm.fvar) =
          (Semiterm.val e f ∘ ω ∘ Semiterm.fvar) := by
        funext y
        simp [Function.comp_def]
      rw [hb, hf]
      exact Iff.rfl
  | _, _, .exs₁ φ, _, ω, E, f, e => by
      refine exists_congr fun x => (eval_rew φ ω.q E f (x :> e)).trans ?_
      have hb : (Semiterm.val (x :> e) f ∘ ω.q ∘ Semiterm.bvar) =
          (x :> (Semiterm.val e f ∘ ω ∘ Semiterm.bvar)) := by
        funext i
        induction i using Fin.cases with
        | zero => simp [Function.comp_def]
        | succ j => simp [Function.comp_def]
      have hf : (Semiterm.val (x :> e) f ∘ ω.q ∘ Semiterm.fvar) =
          (Semiterm.val e f ∘ ω ∘ Semiterm.fvar) := by
        funext y
        simp [Function.comp_def]
      rw [hb, hf]
      exact Iff.rfl
  | _, _, .all₂ φ, _, ω, E, f, e =>
      forall_congr' fun X => imp_congr_right fun _ => eval_rew φ ω (X :> E) f e
  | _, _, .exs₂ φ, _, ω, E, f, e =>
      exists_congr fun X => and_congr Iff.rfl (eval_rew φ ω (X :> E) f e)

/-! ### Evaluation transport for set-variable renaming -/

/-- **Set-valuation transport**: evaluating `bmap g φ` at set valuation `E` is evaluating
`φ` at `E ∘ g` — an explicit transformation of the set valuation, nothing else moves. -/
theorem eval_bmap {𝕊 : Set (Set M)} {F : Ξ → Set M} {f : ξ → M} :
    ∀ {N N' n : ℕ} (φ : SecondOrder.Semiformula L Ξ ξ N n) (g : Fin N → Fin N')
      (E : Fin N' → Set M) (e : Fin n → M),
      ((SecondOrder.Semiformula.bmap g φ).Eval 𝕊 F f E e ↔ φ.Eval 𝕊 F f (E ∘ g) e)
  | _, _, _, .rel R v, g, E, e => Iff.rfl
  | _, _, _, .nrel R v, g, E, e => Iff.rfl
  | _, _, _, .bvar X t, g, E, e => Iff.rfl
  | _, _, _, .nbvar X t, g, E, e => Iff.rfl
  | _, _, _, .fvar X t, g, E, e => Iff.rfl
  | _, _, _, .nfvar X t, g, E, e => Iff.rfl
  | _, _, _, .verum, g, E, e => Iff.rfl
  | _, _, _, .falsum, g, E, e => Iff.rfl
  | _, _, _, .and φ ψ, g, E, e =>
      and_congr (eval_bmap φ g E e) (eval_bmap ψ g E e)
  | _, _, _, .or φ ψ, g, E, e =>
      or_congr (eval_bmap φ g E e) (eval_bmap ψ g E e)
  | _, _, _, .all₁ φ, g, E, e =>
      forall_congr' fun x => eval_bmap φ g E (x :> e)
  | _, _, _, .exs₁ φ, g, E, e =>
      exists_congr fun x => eval_bmap φ g E (x :> e)
  | _, _, _, .all₂ φ, g, E, e =>
      forall_congr' fun X => imp_congr_right fun _ => by
        have h := eval_bmap (𝕊 := 𝕊) (F := F) (f := f) φ (Fin.retrusion g) (X :> E) e
        rw [cons_comp_retrusion] at h
        exact h
  | _, _, _, .exs₂ φ, g, E, e =>
      exists_congr fun X => and_congr Iff.rfl (by
        have h := eval_bmap (𝕊 := 𝕊) (F := F) (f := f) φ (Fin.retrusion g) (X :> E) e
        rw [cons_comp_retrusion] at h
        exact h)

/-- **The critical freshness specialization**: beneath a fresh output-set binder,
`φ.bmap Fin.succ` makes `φ` see the **original** set parameters `E` — never the new set
`X` at index zero. -/
theorem eval_bmap_succ {𝕊 : Set (Set M)} {F : Ξ → Set M} {f : ξ → M} {N n : ℕ}
    (φ : SecondOrder.Semiformula L Ξ ξ N n) (X : Set M) (E : Fin N → Set M)
    (e : Fin n → M) :
    ((SecondOrder.Semiformula.bmap Fin.succ φ).Eval 𝕊 F f (X :> E) e ↔
      φ.Eval 𝕊 F f E e) := by
  rw [eval_bmap φ Fin.succ (X :> E) e]
  have h : (X :> E) ∘ Fin.succ = E := by
    funext i
    simp
  rw [h]

end RMFoundationBridge

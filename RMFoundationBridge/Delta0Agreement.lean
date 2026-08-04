/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import RMFoundationBridge.Delta0Eval

/-!
# F1 item 5, second layer (second slice): the named Tarski-agreement theorem

Review conditions pinned for this commit:

* the theorem is **code-level and unconditional in `c`** — no `IsDelta0` premise, the
  code type carries the invariant;
* bounded quantifiers use `<`, the bound evaluated in the **outer** environment and the
  body under the **extended** environment (`evalN_ballLT`/`evalN_bexLT`);
* positive and negative set atoms both pass through `paramQuery_mem_iff`;
* `List.ofFn` environment ordering is verified explicitly beneath binders (`ofFn_cons`);
* formula-level transport through `c.toFormula = φ` is a separate corollary;
* **no** recursiveness, ideal membership, or `InternalSet` packaging enters this commit —
  `Nat.RecursiveIn` is the next slice.
-/

namespace RMFoundationBridge

open LO LO.FirstOrder LO.SecondOrder
open ReverseMathlib.Omega

/-! ### The oracle answer function (theorem-side only; `beval` stays abstract in `χ`) -/

open Classical in
/-- The membership oracle for a set-parameter assignment: classical decision of
membership in the finite-parameter oracle. Noncomputable by design — it exists for the
agreement theorem; the executable evaluator never depends on it. -/
noncomputable def membershipOracle {N : ℕ} (A : Fin N → Set ℕ) : ℕ → Bool :=
  fun q => decide (q ∈ finiteParamOracle A)

@[simp] theorem membershipOracle_eq_true_iff {N : ℕ} {A : Fin N → Set ℕ} {q : ℕ} :
    membershipOracle A q = true ↔ q ∈ finiteParamOracle A := by
  simp [membershipOracle]

/-! ### The pinned helpers -/

/-- `List.ofFn` after cons is the extended de Bruijn environment. -/
theorem ofFn_cons {n : ℕ} (x : ℕ) (e : Fin n → ℕ) :
    List.ofFn (x :> e) = x :: List.ofFn e := by
  rw [List.ofFn_succ]
  refine congrArg₂ List.cons rfl (congrArg List.ofFn (funext fun i => ?_))
  simp

/-- `List.all` over a range is the bounded universal. -/
theorem all_range_eq_true_iff {b : ℕ} {p : ℕ → Bool} :
    ((List.range b).all p = true) ↔ ∀ x < b, p x = true := by
  simp [List.all_eq_true]

/-- `List.any` over a range is the bounded existential. -/
theorem any_range_eq_true_iff {b : ℕ} {p : ℕ → Bool} :
    ((List.range b).any p = true) ↔ ∃ x < b, p x = true := by
  simp [List.any_eq_true]

/-- Tarski evaluation of the bounded universal: the bound in the **outer** environment,
the body under the **extended** one. -/
theorem evalN_ballLT {𝕊 : Set (Set ℕ)} {N n : ℕ} {t : Semiterm ℒₒᵣ Empty n}
    {φ : SecondOrder.Semiformula ℒₒᵣ Empty Empty N (n + 1)} {E : Fin N → Set ℕ}
    {e : Fin n → ℕ} :
    EvalN 𝕊 (ballLT t φ) E e ↔
      ∀ x : ℕ, x < t.val e Empty.elim → EvalN 𝕊 φ E (x :> e) := by
  rw [show (EvalN 𝕊 (ballLT t φ) E e) =
      (∀ x : ℕ, ¬ (x < (Rew.bShift t).val (x :> e) Empty.elim) ∨ EvalN 𝕊 φ E (x :> e))
    from rfl]
  simp only [Semiterm.val_bShift]
  exact forall_congr' fun x => (imp_iff_not_or).symm

/-- Tarski evaluation of the bounded existential. -/
theorem evalN_bexLT {𝕊 : Set (Set ℕ)} {N n : ℕ} {t : Semiterm ℒₒᵣ Empty n}
    {φ : SecondOrder.Semiformula ℒₒᵣ Empty Empty N (n + 1)} {E : Fin N → Set ℕ}
    {e : Fin n → ℕ} :
    EvalN 𝕊 (bexLT t φ) E e ↔
      ∃ x : ℕ, x < t.val e Empty.elim ∧ EvalN 𝕊 φ E (x :> e) := by
  rw [show (EvalN 𝕊 (bexLT t φ) E e) =
      (∃ x : ℕ, (x < (Rew.bShift t).val (x :> e) Empty.elim) ∧ EvalN 𝕊 φ E (x :> e))
    from rfl]
  simp only [Semiterm.val_bShift]

/-! ### The agreement theorem, code-level and unconditional -/

/-- **Tarski agreement, `= true` form**: the executable evaluator at the membership
oracle agrees with Foundation's Tarski evaluation, for arbitrary code, set assignment,
and number assignment. No `IsDelta0` premise — the code type carries the invariant. -/
theorem beval_eq_true_iff {N : ℕ} (A : Fin N → Set ℕ) (𝕊 : Set (Set ℕ)) :
    ∀ {n : ℕ} (c : Delta0Code N n) (e : Fin n → ℕ),
      (Delta0Code.beval (membershipOracle A) c (List.ofFn e) = true ↔
        EvalN 𝕊 c.toFormula A e)
  | _, .eq t s, e => by
      rw [show Delta0Code.beval (membershipOracle A) (.eq t s) (List.ofFn e) =
            (termValEnv t (List.ofFn e) == termValEnv s (List.ofFn e)) from rfl,
        beq_iff_eq, termValEnv_agrees t e, termValEnv_agrees s e]
      exact Iff.rfl
  | _, .neq t s, e => by
      rw [show Delta0Code.beval (membershipOracle A) (.neq t s) (List.ofFn e) =
            !(termValEnv t (List.ofFn e) == termValEnv s (List.ofFn e)) from rfl,
        Bool.not_eq_true', beq_eq_false_iff_ne, termValEnv_agrees t e,
        termValEnv_agrees s e]
      exact Iff.rfl
  | _, .lt t s, e => by
      rw [show Delta0Code.beval (membershipOracle A) (.lt t s) (List.ofFn e) =
            decide (termValEnv t (List.ofFn e) < termValEnv s (List.ofFn e)) from rfl,
        decide_eq_true_iff, termValEnv_agrees t e, termValEnv_agrees s e]
      exact Iff.rfl
  | _, .nlt t s, e => by
      rw [show Delta0Code.beval (membershipOracle A) (.nlt t s) (List.ofFn e) =
            !decide (termValEnv t (List.ofFn e) < termValEnv s (List.ofFn e)) from rfl,
        Bool.not_eq_true', decide_eq_false_iff_not, termValEnv_agrees t e,
        termValEnv_agrees s e]
      exact Iff.rfl
  | _, .mem X t, e => by
      rw [show Delta0Code.beval (membershipOracle A) (.mem X t) (List.ofFn e) =
            membershipOracle A (paramQuery X (termValEnv t (List.ofFn e))) from rfl,
        membershipOracle_eq_true_iff, paramQuery_mem_iff A X _, termValEnv_agrees t e]
      exact Iff.rfl
  | _, .notMem X t, e => by
      rw [show Delta0Code.beval (membershipOracle A) (.notMem X t) (List.ofFn e) =
            !membershipOracle A (paramQuery X (termValEnv t (List.ofFn e))) from rfl,
        Bool.not_eq_true', Bool.eq_false_iff, ne_eq, membershipOracle_eq_true_iff,
        paramQuery_mem_iff A X _, termValEnv_agrees t e]
      exact Iff.rfl
  | _, .verum, e => by
      simp [Delta0Code.beval]
      exact trivial
  | _, .falsum, e => by
      simp [Delta0Code.beval]
      exact fun h => h
  | _, .and c d, e => by
      rw [show Delta0Code.beval (membershipOracle A) (.and c d) (List.ofFn e) =
            (Delta0Code.beval (membershipOracle A) c (List.ofFn e) &&
              Delta0Code.beval (membershipOracle A) d (List.ofFn e)) from rfl,
        Bool.and_eq_true, beval_eq_true_iff A 𝕊 c e, beval_eq_true_iff A 𝕊 d e]
      exact Iff.rfl
  | _, .or c d, e => by
      rw [show Delta0Code.beval (membershipOracle A) (.or c d) (List.ofFn e) =
            (Delta0Code.beval (membershipOracle A) c (List.ofFn e) ||
              Delta0Code.beval (membershipOracle A) d (List.ofFn e)) from rfl,
        Bool.or_eq_true, beval_eq_true_iff A 𝕊 c e, beval_eq_true_iff A 𝕊 d e]
      exact Iff.rfl
  | _, .ball t c, e => by
      rw [show Delta0Code.beval (membershipOracle A) (.ball t c) (List.ofFn e) =
            ((List.range (termValEnv t (List.ofFn e))).all
              fun x => Delta0Code.beval (membershipOracle A) c
                (x :: List.ofFn e)) from rfl,
        all_range_eq_true_iff, termValEnv_agrees t e]
      rw [show Delta0Code.toFormula (.ball t c) = ballLT t c.toFormula from rfl,
        evalN_ballLT]
      refine forall_congr' fun x => imp_congr Iff.rfl ?_
      rw [← ofFn_cons x e]
      exact beval_eq_true_iff A 𝕊 c (x :> e)
  | _, .bex t c, e => by
      rw [show Delta0Code.beval (membershipOracle A) (.bex t c) (List.ofFn e) =
            ((List.range (termValEnv t (List.ofFn e))).any
              fun x => Delta0Code.beval (membershipOracle A) c
                (x :: List.ofFn e)) from rfl,
        any_range_eq_true_iff, termValEnv_agrees t e]
      rw [show Delta0Code.toFormula (.bex t c) = bexLT t c.toFormula from rfl,
        evalN_bexLT]
      refine exists_congr fun x => and_congr Iff.rfl ?_
      rw [← ofFn_cons x e]
      exact beval_eq_true_iff A 𝕊 c (x :> e)

open Classical in
/-- **The named Tarski-agreement theorem** in the pinned `decide` form: for arbitrary
code, set assignment, and number assignment. -/
theorem beval_agrees {N n : ℕ} (A : Fin N → Set ℕ) (𝕊 : Set (Set ℕ))
    (c : Delta0Code N n) (e : Fin n → ℕ) :
    Delta0Code.beval (membershipOracle A) c (List.ofFn e) =
      decide (EvalN 𝕊 c.toFormula A e) := by
  by_cases h : EvalN 𝕊 c.toFormula A e
  · rw [(beval_eq_true_iff A 𝕊 c e).mpr h, decide_eq_true h]
  · have hb : Delta0Code.beval (membershipOracle A) c (List.ofFn e) = false :=
      Bool.eq_false_iff.mpr fun hb => h ((beval_eq_true_iff A 𝕊 c e).mp hb)
    rw [hb, decide_eq_false h]

/-- **Formula-level transport**, as a separate corollary: agreement carries across
`c.toFormula = φ`. -/
theorem beval_agrees_of_toFormula_eq {N n : ℕ} {A : Fin N → Set ℕ} {𝕊 : Set (Set ℕ)}
    {c : Delta0Code N n} {φ : SecondOrder.Semiformula ℒₒᵣ Empty Empty N n}
    (hc : c.toFormula = φ) (e : Fin n → ℕ) :
    Delta0Code.beval (membershipOracle A) c (List.ofFn e) =
      (letI := Classical.propDecidable
       decide (EvalN 𝕊 φ A e)) := by
  subst hc
  exact beval_agrees A 𝕊 c e

end RMFoundationBridge

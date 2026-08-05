/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import RMFoundationBridge.TreePredicates

/-!
# F2, first layer: internal-object predicates

The EFILC and Hall sentences quantify graph-coded internal functions and consult decoded
finite lists. This layer supplies the shared `ℒₒᵣ` predicates — pair-membership through
a set variable, function-graph-ness (totality and single-valuedness of the coded graph),
decoded-list membership, duplicate-freeness, and non-nilness — each with unconditional
standard-ℕ adequacy terminating at the frozen `ReverseMathlib.Omega` vocabulary
(`Nat.pair`-coded graphs, `decodeSeq`, `getD`, `List.Nodup`). No `OmegaPart`, no
internal sets, no ideal premise; set variables are `Fin N` parameters throughout.
-/

namespace RMFoundationBridge

open LO LO.FirstOrder LO.SecondOrder
open ReverseMathlib.Omega

/-- Negated equality atom (NNF dual). -/
def fNeq {N n : ℕ} (t s : Semiterm ℒₒᵣ Empty n) :
    SecondOrder.Semiformula ℒₒᵣ Empty Empty N n :=
  .nrel Language.ORing.Rel.eq ![t, s]

theorem evalN_fNeq {𝕊 : Set (Set ℕ)} {N n : ℕ} {E : Fin N → Set ℕ}
    {t s : Semiterm ℒₒᵣ Empty n} {e : Fin n → ℕ} :
    EvalN 𝕊 (fNeq (N := N) t s) E e ↔ ¬ tval t e = tval s e := Iff.rfl

/-! ### Pair membership through a set variable -/

/-- `(x, y)`: the pair code `Nat.pair x y` belongs to the set variable `X`. -/
def pairMemFormula {N : ℕ} (X : Fin N) :
    SecondOrder.Semiformula ℒₒᵣ Empty Empty N 2 :=
  .exs₁ (app₃ pairGraph #1 #2 #0 ⋏ .bvar X #0)

section pairMem

variable {𝕊 : Set (Set ℕ)} {N n : ℕ} {E : Fin N → Set ℕ}

theorem evalN_pairMemFormula (X : Fin N) (x y : ℕ) :
    EvalN 𝕊 (pairMemFormula X) E ![x, y] ↔ Nat.pair x y ∈ E X := by
  have h : EvalN 𝕊 (pairMemFormula X) E ![x, y] ↔
      ∃ p : ℕ, EvalN 𝕊 (app₃ pairGraph #1 #2 #0) E (p :> ![x, y]) ∧
        EvalN 𝕊 (.bvar X #0) E (p :> ![x, y]) := Iff.rfl
  rw [h]
  constructor
  · rintro ⟨p, h₁, h₂⟩
    have h₁' : p = Nat.pair x y := (evalN_app₃_pairGraph _ _ _ _).mp h₁
    have h₂' : p ∈ E X := h₂
    rwa [h₁'] at h₂'
  · intro hmem
    exact ⟨Nat.pair x y, (evalN_app₃_pairGraph _ _ _ _).mpr rfl, hmem⟩

theorem evalN_app₂_pairMemFormula (X : Fin N) (t₁ t₂ : Semiterm ℒₒᵣ Empty n)
    (e : Fin n → ℕ) :
    EvalN 𝕊 (app₂ (pairMemFormula X) t₁ t₂) E e ↔
      Nat.pair (tval t₁ e) (tval t₂ e) ∈ E X := by
  rw [evalN_app₂, evalN_pairMemFormula]

end pairMem

/-! ### Function-graph-ness -/

/-- The set variable `X` codes a total single-valued function graph. -/
def funGraphFormula {N : ℕ} (X : Fin N) :
    SecondOrder.Semiformula ℒₒᵣ Empty Empty N 0 :=
  .all₁ (.exs₁ (app₂ (pairMemFormula X) #1 #0)) ⋏
  .all₁ (.all₁ (.all₁ (impF
    (app₂ (pairMemFormula X) #2 #1 ⋏ app₂ (pairMemFormula X) #2 #0)
    (fEq #1 #0))))

section funGraph

variable {𝕊 : Set (Set ℕ)} {N : ℕ} {E : Fin N → Set ℕ}

/-- Adequacy in the unbundled form matching `InternalFunction`'s fields (uncurried
single-valuedness; curry with `and_imp` at consumption sites). -/
theorem evalN_funGraphFormula (X : Fin N) (e : Fin 0 → ℕ) :
    EvalN 𝕊 (funGraphFormula X) E e ↔
      (∀ x, ∃ y, Nat.pair x y ∈ E X) ∧
      (∀ x y y', Nat.pair x y ∈ E X ∧ Nat.pair x y' ∈ E X → y = y') := by
  have h : EvalN 𝕊 (funGraphFormula X) E e ↔
      (∀ x : ℕ, ∃ y : ℕ, EvalN 𝕊 (app₂ (pairMemFormula X) #1 #0) E (y :> x :> e)) ∧
      (∀ x y y' : ℕ, EvalN 𝕊 (impF
          (app₂ (pairMemFormula X) #2 #1 ⋏ app₂ (pairMemFormula X) #2 #0)
          (fEq #1 #0)) E (y' :> y :> x :> e)) := Iff.rfl
  rw [h]
  refine and_congr ?_ ?_
  · exact forall_congr' fun x => exists_congr fun y =>
      evalN_app₂_pairMemFormula X _ _ _
  · refine forall_congr' fun x => forall_congr' fun y => forall_congr' fun y' => ?_
    rw [evalN_impF]
    have h2 : EvalN 𝕊 (app₂ (pairMemFormula X) #2 #1 ⋏
        app₂ (pairMemFormula X) #2 #0) E (y' :> y :> x :> e) ↔
        EvalN 𝕊 (app₂ (pairMemFormula X) #2 #1) E (y' :> y :> x :> e) ∧
        EvalN 𝕊 (app₂ (pairMemFormula X) #2 #0) E (y' :> y :> x :> e) := Iff.rfl
    rw [h2]
    exact imp_congr
      (and_congr (evalN_app₂_pairMemFormula X _ _ _) (evalN_app₂_pairMemFormula X _ _ _))
      Iff.rfl

end funGraph

/-! ### Decoded-list membership, duplicate-freeness, non-nilness -/

/-- `(c, x)`: `x` is an entry of the decoded sequence of `c`. -/
def memSeqFormula {N : ℕ} : SecondOrder.Semiformula ℒₒᵣ Empty Empty N 2 :=
  .exs₁ (app₂ seqLenGraph #1 #0 ⋏ bexLT #0 (app₃ seqEntGraph #2 #0 #3))

/-- `(c)`: the decoded sequence of `c` is duplicate-free. -/
def nodupFormula {N : ℕ} : SecondOrder.Semiformula ℒₒᵣ Empty Empty N 1 :=
  .all₁ (impF (app₂ seqLenGraph #1 #0)
    (ballLT #0 (ballLT #0 (.all₁ (.all₁ (impF
      (app₃ seqEntGraph #5 #3 #1 ⋏ app₃ seqEntGraph #5 #2 #0)
      (fNeq #1 #0)))))))

/-- `(c)`: the decoded sequence of `c` is nonempty. -/
def nonNilFormula {N : ℕ} : SecondOrder.Semiformula ℒₒᵣ Empty Empty N 1 :=
  .exs₁ (app₂ seqLenGraph #1 #0 ⋏ fLt tZero #0)

section listPredicates

variable {𝕊 : Set (Set ℕ)} {N n : ℕ} {E : Fin N → Set ℕ}

/-- The `getD` characterization of membership. -/
theorem mem_char {c x : ℕ} :
    (∃ m, (decodeSeq c).length = m ∧ ∃ i < m, (decodeSeq c).getD i 0 = x) ↔
      x ∈ decodeSeq c := by
  constructor
  · rintro ⟨m, rfl, i, hi, hx⟩
    rw [getD_of_lt hi] at hx
    rw [← hx]
    exact List.getElem_mem hi
  · intro hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    exact ⟨(decodeSeq c).length, rfl, i, hi, getD_of_lt hi⟩

theorem evalN_memSeqFormula (c x : ℕ) :
    EvalN 𝕊 (memSeqFormula (N := N)) E ![c, x] ↔ x ∈ decodeSeq c := by
  have h : EvalN 𝕊 (memSeqFormula (N := N)) E ![c, x] ↔
      ∃ m : ℕ, EvalN 𝕊 (app₂ seqLenGraph #1 #0) E (m :> ![c, x]) ∧
        EvalN 𝕊 (bexLT #0 (app₃ seqEntGraph #2 #0 #3)) E (m :> ![c, x]) := Iff.rfl
  rw [h, ← mem_char]
  refine exists_congr fun m => and_congr (evalN_app₂_seqLenGraph _ _ _) ?_
  rw [evalN_bexLT]
  exact exists_congr fun i => and_congr Iff.rfl (evalN_app₃_seqEntGraph _ _ _ _)

theorem evalN_app₂_memSeqFormula (t₁ t₂ : Semiterm ℒₒᵣ Empty n) (e : Fin n → ℕ) :
    EvalN 𝕊 (app₂ (memSeqFormula (N := N)) t₁ t₂) E e ↔
      tval t₂ e ∈ decodeSeq (tval t₁ e) := by
  rw [evalN_app₂, evalN_memSeqFormula]

/-- The entrywise characterization of `Nodup`. -/
theorem nodup_char {l : List ℕ} :
    (∀ m, l.length = m → ∀ i < m, ∀ j < i, ∀ a b,
      l.getD i 0 = a ∧ l.getD j 0 = b → ¬ a = b) ↔ l.Nodup := by
  constructor
  · intro h
    rw [List.nodup_iff_injective_getElem]
    rintro ⟨i, hi⟩ ⟨j, hj⟩ hab
    have hab' : l[i] = l[j] := hab
    rcases Nat.lt_trichotomy i j with hlt | heq | hgt
    · exact absurd hab'.symm
        (h l.length rfl j hj i hlt l[j] l[i] ⟨getD_of_lt hj, getD_of_lt hi⟩)
    · exact Fin.ext heq
    · exact absurd hab'
        (h l.length rfl i hi j hgt l[i] l[j] ⟨getD_of_lt hi, getD_of_lt hj⟩)
  · rintro h m rfl i hi j hij a b ⟨ha, hb⟩ hab
    have hja : j < l.length := Nat.lt_trans hij hi
    rw [getD_of_lt hi] at ha
    rw [getD_of_lt hja] at hb
    have heq : l[i] = l[j] := by rw [ha, hb, hab]
    have hfin := List.nodup_iff_injective_getElem.mp h
      (a₁ := ⟨i, hi⟩) (a₂ := ⟨j, hja⟩) heq
    have hij' : i = j := congrArg Fin.val hfin
    omega

theorem evalN_nodupFormula (c : ℕ) :
    EvalN 𝕊 (nodupFormula (N := N)) E ![c] ↔ (decodeSeq c).Nodup := by
  have h : EvalN 𝕊 (nodupFormula (N := N)) E ![c] ↔
      ∀ m : ℕ, EvalN 𝕊 (impF (app₂ seqLenGraph #1 #0)
        (ballLT #0 (ballLT #0 (.all₁ (.all₁ (impF
          (app₃ seqEntGraph #5 #3 #1 ⋏ app₃ seqEntGraph #5 #2 #0)
          (fNeq #1 #0))))))) E (m :> ![c]) := Iff.rfl
  rw [h, ← nodup_char]
  refine forall_congr' fun m => ?_
  rw [evalN_impF]
  refine imp_congr (evalN_app₂_seqLenGraph _ _ _) ?_
  rw [evalN_ballLT]
  refine forall_congr' fun i => imp_congr Iff.rfl ?_
  rw [evalN_ballLT]
  refine forall_congr' fun j => imp_congr Iff.rfl ?_
  have h2 : EvalN 𝕊 (.all₁ (.all₁ (impF
      (app₃ seqEntGraph #5 #3 #1 ⋏ app₃ seqEntGraph #5 #2 #0)
      (fNeq #1 #0)))) E (j :> i :> m :> ![c]) ↔
      ∀ a b : ℕ, EvalN 𝕊 (impF
        (app₃ seqEntGraph #5 #3 #1 ⋏ app₃ seqEntGraph #5 #2 #0)
        (fNeq #1 #0)) E (b :> a :> j :> i :> m :> ![c]) := Iff.rfl
  rw [h2]
  refine forall_congr' fun a => forall_congr' fun b => ?_
  rw [evalN_impF]
  have h3 : EvalN 𝕊 (app₃ seqEntGraph #5 #3 #1 ⋏ app₃ seqEntGraph #5 #2 #0) E
      (b :> a :> j :> i :> m :> ![c]) ↔
      EvalN 𝕊 (app₃ seqEntGraph #5 #3 #1) E (b :> a :> j :> i :> m :> ![c]) ∧
      EvalN 𝕊 (app₃ seqEntGraph #5 #2 #0) E (b :> a :> j :> i :> m :> ![c]) := Iff.rfl
  rw [h3]
  exact imp_congr
    (and_congr (evalN_app₃_seqEntGraph _ _ _ _) (evalN_app₃_seqEntGraph _ _ _ _))
    Iff.rfl

theorem evalN_app₁_nodupFormula (t₁ : Semiterm ℒₒᵣ Empty n) (e : Fin n → ℕ) :
    EvalN 𝕊 (app₁ (nodupFormula (N := N)) t₁) E e ↔
      (decodeSeq (tval t₁ e)).Nodup := by
  rw [evalN_app₁, evalN_nodupFormula]

theorem evalN_nonNilFormula (c : ℕ) :
    EvalN 𝕊 (nonNilFormula (N := N)) E ![c] ↔ decodeSeq c ≠ [] := by
  have h : EvalN 𝕊 (nonNilFormula (N := N)) E ![c] ↔
      ∃ m : ℕ, EvalN 𝕊 (app₂ seqLenGraph #1 #0) E (m :> ![c]) ∧
        EvalN 𝕊 (fLt tZero #0) E (m :> ![c]) := Iff.rfl
  rw [h]
  constructor
  · rintro ⟨m, hm, h0⟩ hnil
    have hm' : (decodeSeq c).length = m := (evalN_app₂_seqLenGraph _ _ _).mp hm
    have h0' : 0 < m := h0
    rw [hnil] at hm'
    simp at hm'
    omega
  · intro hne
    refine ⟨(decodeSeq c).length, (evalN_app₂_seqLenGraph _ _ _).mpr rfl, ?_⟩
    show 0 < (decodeSeq c).length
    exact Nat.pos_of_ne_zero fun h0 => hne (List.eq_nil_of_length_eq_zero h0)

theorem evalN_app₁_nonNilFormula (t₁ : Semiterm ℒₒᵣ Empty n) (e : Fin n → ℕ) :
    EvalN 𝕊 (app₁ (nonNilFormula (N := N)) t₁) E e ↔
      decodeSeq (tval t₁ e) ≠ [] := by
  rw [evalN_app₁, evalN_nonNilFormula]

end listPredicates

end RMFoundationBridge

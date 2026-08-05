/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Omega.Hall
import RMFoundationBridge.EfilcSentence

/-!
# F2, third layer: the one-sided Hall sentence and the unconditional adapter

`hallSentence` is exact countable Hall as a closed `ℒₒᵣ` second-order sentence, spelled
against the **frozen** `InternalHallFamily`: the quantified sets are the candidate
relation and the enumerator graph; the hypothesis carries function-graph-ness, enum
nodup, the checked membership equivalence, and the **arithmetized marriage condition**;
the conclusion asks for an injective transversal graph. One-sided exactly as frozen:
marriage implies transversal, nothing else.

**The marriage arithmetization** (`marriageFormula`/`MarriageN`/`marriage_char`): the
frozen condition quantifies an ambient `Finset ℕ` and an ambient witness function
`w : ℕ → ℕ`; the sentence quantifies a nodup coded index list `sc` and a parallel coded
list `wc` of enumerated candidate codes, and expresses the cardinality comparison as
existence of a nodup coded list of the same length covered by the candidate lists —
a subset of the union of size `|s|` is the same thing as such a list. `marriage_char`
proves the two forms equivalent over standard ℕ, with the witness function recovered
from the coded lists by `idxOf` and the covering list extracted from the union by
`Finset.exists_subset_card_eq`. No choice of transversal, no selection — witnesses only.

**`models_hallSentence_iff` is unconditional**: for arbitrary `Ω`, satisfaction is
exactly the frozen `CountableHallAt Ω`. No Turing-ideal premise, no derivation claims.
-/

namespace RMFoundationBridge

open LO LO.FirstOrder LO.SecondOrder
open ReverseMathlib.Omega

/-! ### The marriage condition, arithmetized -/

/-- Pointwise enumeration: entry `i` of the index list is enumerated by entry `i` of the
candidate-code list, through the set variable `0`. -/
def marriagePointwise : SecondOrder.Semiformula ℒₒᵣ Empty Empty 2 6 :=
  impF (app₃ seqEntGraph #5 #2 #1 ⋏ app₃ seqEntGraph #4 #2 #0)
    (app₂ (pairMemFormula 0) #1 #0)

/-- The marriage antecedent: `sc` nodup, both lists of length `k`, pointwise
enumerated. -/
def marriageAnt : SecondOrder.Semiformula ℒₒᵣ Empty Empty 2 3 :=
  app₁ nodupFormula #2 ⋏ app₂ seqLenGraph #2 #0 ⋏ app₂ seqLenGraph #1 #0 ⋏
  ballLT #0 (.all₁ (.all₁ marriagePointwise))

/-- One covering entry: an entry of the distinct-witness list lies in some candidate
list. -/
def marriageCover : SecondOrder.Semiformula ℒₒᵣ Empty Empty 2 6 :=
  impF (app₃ seqEntGraph #2 #1 #0)
    (bexLT #3 (.exs₁ (app₃ seqEntGraph #6 #1 #0 ⋏ app₂ memSeqFormula #0 #2)))

/-- The marriage consequent: a nodup list of length `k` covered by the candidate
lists. -/
def marriageCon : SecondOrder.Semiformula ℒₒᵣ Empty Empty 2 3 :=
  .exs₁ (app₂ seqLenGraph #0 #1 ⋏ app₁ nodupFormula #0 ⋏
    ballLT #1 (.all₁ marriageCover))

/-- The arithmetized marriage condition over the set variable `0`. -/
def marriageFormula : SecondOrder.Semiformula ℒₒᵣ Empty Empty 2 0 :=
  .all₁ (.all₁ (.all₁ (impF marriageAnt marriageCon)))

/-- The coded-list reading of the marriage condition. -/
def MarriageN (Ge : Set ℕ) : Prop :=
  ∀ sc wc k : ℕ,
    ((decodeSeq sc).Nodup ∧ (decodeSeq sc).length = k ∧ (decodeSeq wc).length = k ∧
      ∀ i < k, ∀ a b, (decodeSeq sc).getD i 0 = a ∧ (decodeSeq wc).getD i 0 = b →
        Nat.pair a b ∈ Ge) →
    ∃ dc, (decodeSeq dc).length = k ∧ (decodeSeq dc).Nodup ∧
      ∀ i < k, ∀ a, (decodeSeq dc).getD i 0 = a →
        ∃ j < k, ∃ b, (decodeSeq wc).getD j 0 = b ∧ a ∈ decodeSeq b

section marriage

variable {𝕊 : Set (Set ℕ)}

theorem evalN_marriageFormula (Ge R : Set ℕ) (e : Fin 0 → ℕ) :
    EvalN 𝕊 marriageFormula ![Ge, R] e ↔ MarriageN Ge := by
  have h : EvalN 𝕊 marriageFormula ![Ge, R] e ↔
      ∀ sc wc k : ℕ, EvalN 𝕊 (impF marriageAnt marriageCon) ![Ge, R]
        (k :> wc :> sc :> e) := Iff.rfl
  rw [h]
  refine forall_congr' fun sc => forall_congr' fun wc => forall_congr' fun k => ?_
  rw [evalN_impF]
  have hant : EvalN 𝕊 marriageAnt ![Ge, R] (k :> wc :> sc :> e) ↔
      ((decodeSeq sc).Nodup ∧ (decodeSeq sc).length = k ∧
        (decodeSeq wc).length = k ∧
        ∀ i < k, ∀ a b, (decodeSeq sc).getD i 0 = a ∧ (decodeSeq wc).getD i 0 = b →
          Nat.pair a b ∈ Ge) := by
    have h2 : EvalN 𝕊 marriageAnt ![Ge, R] (k :> wc :> sc :> e) ↔
        EvalN 𝕊 (app₁ nodupFormula #2) ![Ge, R] (k :> wc :> sc :> e) ∧
        EvalN 𝕊 (app₂ seqLenGraph #2 #0) ![Ge, R] (k :> wc :> sc :> e) ∧
        EvalN 𝕊 (app₂ seqLenGraph #1 #0) ![Ge, R] (k :> wc :> sc :> e) ∧
        EvalN 𝕊 (ballLT #0 (.all₁ (.all₁ marriagePointwise))) ![Ge, R]
          (k :> wc :> sc :> e) := Iff.rfl
    rw [h2]
    refine and_congr (evalN_app₁_nodupFormula _ _) (and_congr
      (evalN_app₂_seqLenGraph _ _ _) (and_congr (evalN_app₂_seqLenGraph _ _ _) ?_))
    rw [evalN_ballLT]
    refine forall_congr' fun i => imp_congr Iff.rfl ?_
    have h3 : EvalN 𝕊 (.all₁ (.all₁ marriagePointwise)) ![Ge, R]
        (i :> k :> wc :> sc :> e) ↔
        ∀ a b : ℕ, EvalN 𝕊 marriagePointwise ![Ge, R]
          (b :> a :> i :> k :> wc :> sc :> e) := Iff.rfl
    rw [h3]
    refine forall_congr' fun a => forall_congr' fun b => ?_
    rw [show marriagePointwise =
      impF (app₃ seqEntGraph #5 #2 #1 ⋏ app₃ seqEntGraph #4 #2 #0)
        (app₂ (pairMemFormula 0) #1 #0) from rfl, evalN_impF]
    have h4 : EvalN 𝕊 (app₃ seqEntGraph #5 #2 #1 ⋏ app₃ seqEntGraph #4 #2 #0)
        ![Ge, R] (b :> a :> i :> k :> wc :> sc :> e) ↔
        EvalN 𝕊 (app₃ seqEntGraph #5 #2 #1) ![Ge, R]
          (b :> a :> i :> k :> wc :> sc :> e) ∧
        EvalN 𝕊 (app₃ seqEntGraph #4 #2 #0) ![Ge, R]
          (b :> a :> i :> k :> wc :> sc :> e) := Iff.rfl
    rw [h4]
    exact imp_congr
      (and_congr (evalN_app₃_seqEntGraph _ _ _ _) (evalN_app₃_seqEntGraph _ _ _ _))
      (evalN_app₂_pairMemFormula 0 _ _ _)
  have hcon : EvalN 𝕊 marriageCon ![Ge, R] (k :> wc :> sc :> e) ↔
      (∃ dc, (decodeSeq dc).length = k ∧ (decodeSeq dc).Nodup ∧
        ∀ i < k, ∀ a, (decodeSeq dc).getD i 0 = a →
          ∃ j < k, ∃ b, (decodeSeq wc).getD j 0 = b ∧ a ∈ decodeSeq b) := by
    have h2 : EvalN 𝕊 marriageCon ![Ge, R] (k :> wc :> sc :> e) ↔
        ∃ dc : ℕ,
          EvalN 𝕊 (app₂ seqLenGraph #0 #1) ![Ge, R] (dc :> k :> wc :> sc :> e) ∧
          EvalN 𝕊 (app₁ nodupFormula #0) ![Ge, R] (dc :> k :> wc :> sc :> e) ∧
          EvalN 𝕊 (ballLT #1 (.all₁ marriageCover)) ![Ge, R]
            (dc :> k :> wc :> sc :> e) := Iff.rfl
    rw [h2]
    refine exists_congr fun dc => and_congr (evalN_app₂_seqLenGraph _ _ _)
      (and_congr (evalN_app₁_nodupFormula _ _) ?_)
    rw [evalN_ballLT]
    refine forall_congr' fun i => imp_congr Iff.rfl ?_
    have h3 : EvalN 𝕊 (.all₁ marriageCover) ![Ge, R]
        (i :> dc :> k :> wc :> sc :> e) ↔
        ∀ a : ℕ, EvalN 𝕊 marriageCover ![Ge, R]
          (a :> i :> dc :> k :> wc :> sc :> e) := Iff.rfl
    rw [h3]
    refine forall_congr' fun a => ?_
    rw [show marriageCover = impF (app₃ seqEntGraph #2 #1 #0)
      (bexLT #3 (.exs₁ (app₃ seqEntGraph #6 #1 #0 ⋏ app₂ memSeqFormula #0 #2)))
      from rfl, evalN_impF]
    refine imp_congr (evalN_app₃_seqEntGraph _ _ _ _) ?_
    rw [evalN_bexLT]
    refine exists_congr fun j => and_congr Iff.rfl ?_
    have h4 : EvalN 𝕊 (.exs₁ (app₃ seqEntGraph #6 #1 #0 ⋏ app₂ memSeqFormula #0 #2))
        ![Ge, R] (j :> a :> i :> dc :> k :> wc :> sc :> e) ↔
        ∃ b : ℕ,
          EvalN 𝕊 (app₃ seqEntGraph #6 #1 #0) ![Ge, R]
            (b :> j :> a :> i :> dc :> k :> wc :> sc :> e) ∧
          EvalN 𝕊 (app₂ memSeqFormula #0 #2) ![Ge, R]
            (b :> j :> a :> i :> dc :> k :> wc :> sc :> e) := Iff.rfl
    rw [h4]
    exact exists_congr fun b => and_congr (evalN_app₃_seqEntGraph _ _ _ _)
      (evalN_app₂_memSeqFormula _ _ _)
  rw [hant, hcon]

/-- **The marriage characterization**: the coded-list reading is the frozen
`Finset`-and-witness-function reading, over standard ℕ. -/
theorem marriage_char {Ge : Set ℕ} :
    MarriageN Ge ↔
      ∀ (s : Finset ℕ) (w : ℕ → ℕ), (∀ n ∈ s, Nat.pair n (w n) ∈ Ge) →
        s.card ≤ (s.biUnion fun n => (decodeSeq (w n)).toFinset).card := by
  constructor
  · intro hM s w hw
    have hant : (decodeSeq (seqCode s.toList)).Nodup ∧
        (decodeSeq (seqCode s.toList)).length = s.card ∧
        (decodeSeq (seqCode (s.toList.map w))).length = s.card ∧
        ∀ i < s.card, ∀ a b,
          (decodeSeq (seqCode s.toList)).getD i 0 = a ∧
          (decodeSeq (seqCode (s.toList.map w))).getD i 0 = b →
          Nat.pair a b ∈ Ge := by
      refine ⟨by rw [decodeSeq_seqCode]; exact s.nodup_toList,
        by rw [decodeSeq_seqCode]; exact s.length_toList,
        by rw [decodeSeq_seqCode, List.length_map]; exact s.length_toList, ?_⟩
      rintro i hi a b ⟨ha, hb⟩
      rw [decodeSeq_seqCode] at ha hb
      have hi' : i < s.toList.length := by rw [s.length_toList]; exact hi
      have hi'' : i < (s.toList.map w).length := by
        rw [List.length_map, s.length_toList]; exact hi
      rw [getD_of_lt hi'] at ha
      rw [getD_of_lt hi'', List.getElem_map] at hb
      rw [← ha, ← hb]
      exact hw _ (Finset.mem_toList.mp (List.getElem_mem hi'))
    obtain ⟨dc, hlen, hnd, hcover⟩ := hM (seqCode s.toList)
      (seqCode (s.toList.map w)) s.card hant
    have hsub : (decodeSeq dc).toFinset ⊆
        s.biUnion fun n => (decodeSeq (w n)).toFinset := by
      intro a ha
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (List.mem_toFinset.mp ha)
      have hik : i < s.card := by rw [← hlen]; exact hi
      obtain ⟨j, hj, b, hb, hab⟩ := hcover i hik _ (getD_of_lt hi)
      have hj' : j < (s.toList.map w).length := by
        rw [List.length_map, s.length_toList]; exact hj
      rw [decodeSeq_seqCode, getD_of_lt hj', List.getElem_map] at hb
      have hj'' : j < s.toList.length := by rw [s.length_toList]; exact hj
      refine Finset.mem_biUnion.mpr ⟨s.toList[j],
        Finset.mem_toList.mp (List.getElem_mem hj''), ?_⟩
      rw [← hb] at hab
      exact List.mem_toFinset.mpr hab
    calc s.card = (decodeSeq dc).toFinset.card := by
          rw [List.toFinset_card_of_nodup hnd, hlen]
      _ ≤ _ := Finset.card_le_card hsub
  · intro hfz sc wc k ⟨hnd, hlsc, hlwc, hpw⟩
    set s : Finset ℕ := (decodeSeq sc).toFinset with hs
    set w : ℕ → ℕ := fun x => (decodeSeq wc).getD ((decodeSeq sc).idxOf x) 0 with hwdef
    have hw : ∀ n ∈ s, Nat.pair n (w n) ∈ Ge := by
      intro n hn
      have hmem : n ∈ decodeSeq sc := List.mem_toFinset.mp hn
      have hi : (decodeSeq sc).idxOf n < (decodeSeq sc).length :=
        List.idxOf_lt_length_of_mem hmem
      refine hpw ((decodeSeq sc).idxOf n) (by rw [← hlsc]; exact hi) n (w n)
        ⟨?_, rfl⟩
      rw [getD_of_lt hi]
      exact List.getElem_idxOf hi
    have hcard := hfz s w hw
    have hscard : s.card = k := by
      rw [hs, List.toFinset_card_of_nodup hnd, hlsc]
    obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq
      (show k ≤ (s.biUnion fun n => (decodeSeq (w n)).toFinset).card from
        hscard ▸ hcard)
    refine ⟨seqCode t.toList, by rw [decodeSeq_seqCode, t.length_toList, htc],
      by rw [decodeSeq_seqCode]; exact t.nodup_toList, ?_⟩
    rintro i hi a ha
    rw [decodeSeq_seqCode] at ha
    have hi' : i < t.toList.length := by rw [t.length_toList, htc]; exact hi
    rw [getD_of_lt hi'] at ha
    have hat : a ∈ t := by rw [← ha]; exact Finset.mem_toList.mp (List.getElem_mem hi')
    obtain ⟨n, hns, han⟩ := Finset.mem_biUnion.mp (hts hat)
    have hnmem : n ∈ decodeSeq sc := List.mem_toFinset.mp hns
    have hj : (decodeSeq sc).idxOf n < (decodeSeq sc).length :=
      List.idxOf_lt_length_of_mem hnmem
    exact ⟨(decodeSeq sc).idxOf n, by rw [← hlsc]; exact hj, w n, rfl,
      List.mem_toFinset.mp han⟩

end marriage

/-! ### The hypothesis and conclusion matrices -/

/-- The family hypothesis at set scope `(Ge, R) = (0, 1)`: the enumerator is a function
graph, enumerations are nodup, the checked membership equivalence holds, and the
marriage condition holds. -/
def hallHypFormula : SecondOrder.Semiformula ℒₒᵣ Empty Empty 2 0 :=
  funGraphFormula 0 ⋏
  .all₁ (.all₁ (impF (app₂ (pairMemFormula 0) #1 #0) (app₁ nodupFormula #0))) ⋏
  .all₁ (.all₁ (.all₁ (impF (app₂ (pairMemFormula 0) #2 #1)
    (iffF (app₂ memSeqFormula #1 #0) (app₂ (pairMemFormula 1) #2 #0))))) ⋏
  marriageFormula

/-- The transversal conclusion at set scope `(Gt, Ge, R) = (0, 1, 2)`. -/
def hallConclFormula : SecondOrder.Semiformula ℒₒᵣ Empty Empty 3 0 :=
  funGraphFormula 0 ⋏
  .all₁ (.all₁ (impF (app₂ (pairMemFormula 0) #1 #0)
    (app₂ (pairMemFormula 2) #1 #0))) ⋏
  .all₁ (.all₁ (.all₁ (impF
    (app₂ (pairMemFormula 0) #2 #0 ⋏ app₂ (pairMemFormula 0) #1 #0)
    (fEq #2 #1))))

/-- **The one-sided Hall sentence**: every internally presented family satisfying the
marriage condition has an injective transversal. -/
def hallSentence : SecondOrder.Sentence ℒₒᵣ :=
  .all₂ (.all₂ (impF hallHypFormula (.exs₂ hallConclFormula)))

section matrices

variable {𝕊 : Set (Set ℕ)}

/-- Hypothesis adequacy, unbundled to the frozen record fields plus `MarriageN`. -/
theorem evalN_hallHypFormula (Ge R : Set ℕ) (e : Fin 0 → ℕ) :
    EvalN 𝕊 hallHypFormula ![Ge, R] e ↔
      ((∀ x, ∃ y, Nat.pair x y ∈ Ge) ∧
        (∀ x y y', Nat.pair x y ∈ Ge ∧ Nat.pair x y' ∈ Ge → y = y')) ∧
      (∀ m c, Nat.pair m c ∈ Ge → (decodeSeq c).Nodup) ∧
      (∀ m c y, Nat.pair m c ∈ Ge → (y ∈ decodeSeq c ↔ Nat.pair m y ∈ R)) ∧
      MarriageN Ge := by
  have h : EvalN 𝕊 hallHypFormula ![Ge, R] e ↔
      EvalN 𝕊 (funGraphFormula 0) ![Ge, R] e ∧
      (∀ m c : ℕ, EvalN 𝕊 (impF (app₂ (pairMemFormula 0) #1 #0)
        (app₁ nodupFormula #0)) ![Ge, R] (c :> m :> e)) ∧
      (∀ m c y : ℕ, EvalN 𝕊 (impF (app₂ (pairMemFormula 0) #2 #1)
        (iffF (app₂ memSeqFormula #1 #0) (app₂ (pairMemFormula 1) #2 #0))) ![Ge, R]
        (y :> c :> m :> e)) ∧
      EvalN 𝕊 marriageFormula ![Ge, R] e := Iff.rfl
  rw [h]
  refine and_congr (evalN_funGraphFormula 0 e) (and_congr ?_ (and_congr ?_
    (evalN_marriageFormula Ge R e)))
  · refine forall_congr' fun m => forall_congr' fun c => ?_
    rw [evalN_impF]
    exact imp_congr (evalN_app₂_pairMemFormula 0 _ _ _) (evalN_app₁_nodupFormula _ _)
  · refine forall_congr' fun m => forall_congr' fun c => forall_congr' fun y => ?_
    rw [evalN_impF]
    refine imp_congr (evalN_app₂_pairMemFormula 0 _ _ _) ?_
    rw [evalN_iffF]
    exact iff_congr (evalN_app₂_memSeqFormula _ _ _)
      (evalN_app₂_pairMemFormula 1 _ _ _)

/-- Conclusion adequacy, unbundled to the frozen `IsTransversal` conditions. -/
theorem evalN_hallConclFormula (Gt Ge R : Set ℕ) (e : Fin 0 → ℕ) :
    EvalN 𝕊 hallConclFormula ![Gt, Ge, R] e ↔
      ((∀ x, ∃ y, Nat.pair x y ∈ Gt) ∧
        (∀ x y y', Nat.pair x y ∈ Gt ∧ Nat.pair x y' ∈ Gt → y = y')) ∧
      (∀ m y, Nat.pair m y ∈ Gt → Nat.pair m y ∈ R) ∧
      (∀ m m' y, Nat.pair m y ∈ Gt ∧ Nat.pair m' y ∈ Gt → m = m') := by
  have h : EvalN 𝕊 hallConclFormula ![Gt, Ge, R] e ↔
      EvalN 𝕊 (funGraphFormula 0) ![Gt, Ge, R] e ∧
      (∀ m y : ℕ, EvalN 𝕊 (impF (app₂ (pairMemFormula 0) #1 #0)
        (app₂ (pairMemFormula 2) #1 #0)) ![Gt, Ge, R] (y :> m :> e)) ∧
      (∀ m m' y : ℕ, EvalN 𝕊 (impF
        (app₂ (pairMemFormula 0) #2 #0 ⋏ app₂ (pairMemFormula 0) #1 #0)
        (fEq #2 #1)) ![Gt, Ge, R] (y :> m' :> m :> e)) := Iff.rfl
  rw [h]
  refine and_congr (evalN_funGraphFormula 0 e) (and_congr ?_ ?_)
  · refine forall_congr' fun m => forall_congr' fun y => ?_
    rw [evalN_impF]
    exact imp_congr (evalN_app₂_pairMemFormula 0 _ _ _)
      (evalN_app₂_pairMemFormula 2 _ _ _)
  · refine forall_congr' fun m => forall_congr' fun m' => forall_congr' fun y => ?_
    rw [evalN_impF]
    have h2 : EvalN 𝕊 (app₂ (pairMemFormula 0) #2 #0 ⋏
        app₂ (pairMemFormula 0) #1 #0) ![Gt, Ge, R] (y :> m' :> m :> e) ↔
        EvalN 𝕊 (app₂ (pairMemFormula 0) #2 #0) ![Gt, Ge, R] (y :> m' :> m :> e) ∧
        EvalN 𝕊 (app₂ (pairMemFormula 0) #1 #0) ![Gt, Ge, R] (y :> m' :> m :> e) :=
      Iff.rfl
    rw [h2]
    exact imp_congr
      (and_congr (evalN_app₂_pairMemFormula 0 _ _ _)
        (evalN_app₂_pairMemFormula 0 _ _ _))
      Iff.rfl

end matrices

/-! ### The unconditional adapter -/

/-- **The unconditional statement adapter for one-sided Hall**: for an arbitrary
second-order part, satisfaction of the Hall sentence is exactly the frozen
`CountableHallAt`. -/
theorem models_hallSentence_iff {Ω : OmegaPart} :
    Ω.toFoundation ⊧ hallSentence ↔ CountableHallAt Ω := by
  have h : Ω.toFoundation ⊧ hallSentence ↔
      ∀ R : Set ℕ, R ∈ Ω.sets → ∀ Ge : Set ℕ, Ge ∈ Ω.sets →
        EvalN Ω.sets (impF hallHypFormula (.exs₂ hallConclFormula))
          ![Ge, R] ![] := Iff.rfl
  rw [h]
  constructor
  · intro hf H hmar
    have hH := hf H.relation.1 H.relation.2 H.enum.graph.1 H.enum.graph.2
    rw [evalN_impF] at hH
    have hhyp := (evalN_hallHypFormula (𝕊 := Ω.sets)
        H.enum.graph.1 H.relation.1 ![]).mpr
      ⟨⟨H.enum.total, fun x y y' hp => H.enum.singleValued x y y' hp.1 hp.2⟩,
       fun m c hc => H.enum_nodup m c hc,
       fun m c y hc => H.mem_iff m c y hc,
       marriage_char.mpr hmar⟩
    obtain ⟨Gt, hGt, hconcl⟩ := hH hhyp
    have hc := (evalN_hallConclFormula (𝕊 := Ω.sets)
      Gt H.enum.graph.1 H.relation.1 ![]).mp hconcl
    refine ⟨⟨⟨Gt, hGt⟩, hc.1.1, fun x y y' h1 h2 => hc.1.2 x y y' ⟨h1, h2⟩⟩, ?_, ?_⟩
    · exact fun m y hm => hc.2.1 m y hm
    · exact fun m m' y hm hm' => hc.2.2 m m' y ⟨hm, hm'⟩
  · intro hE R hR Ge hGe
    rw [evalN_impF]
    intro hhyp
    have hh := (evalN_hallHypFormula (𝕊 := Ω.sets) Ge R ![]).mp hhyp
    set H : InternalHallFamily Ω :=
      { relation := ⟨R, hR⟩
        enum := ⟨⟨Ge, hGe⟩, hh.1.1, fun x y y' h1 h2 => hh.1.2 x y y' ⟨h1, h2⟩⟩
        enum_nodup := fun m c hc => hh.2.1 m c hc
        mem_iff := fun m c y hc => hh.2.2.1 m c y hc } with hHdef
    obtain ⟨f, hf⟩ := hE H (marriage_char.mp hh.2.2.2)
    refine ⟨f.graph.1, f.graph.2, ?_⟩
    refine (evalN_hallConclFormula (𝕊 := Ω.sets) f.graph.1 Ge R ![]).mpr
      ⟨⟨f.total, fun x y y' hp => f.singleValued x y y' hp.1 hp.2⟩, ?_, ?_⟩
    · exact fun m y hm => hf.1 m y hm
    · exact fun m m' y hp => hf.2 m m' y hp.1 hp.2

end RMFoundationBridge

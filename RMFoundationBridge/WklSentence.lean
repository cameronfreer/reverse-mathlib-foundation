/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import RMFoundationBridge.TreePredicates

/-!
# F1 step 4, third layer: the closed ŴKL sentence and the unconditional adapter

`wklSentence` is the exact binary-tree weak Kőnig's lemma as a closed `ℒₒᵣ` second-order
sentence: every binary tree with a node at every level has a path, with tree, level, and
path spelled by the second-layer predicates over the **frozen** coding.

**`models_wklSentence_iff` is unconditional**: for an *arbitrary* second-order part `Ω`
— no Turing-ideal premise, no closure assumption — satisfaction of `wklSentence` in
`Ω.toFoundation` is exactly the frozen `WeakKonigAt Ω`. The second-order quantifiers
already range over `Ω.sets`, and the number coding agrees literally with the frozen
endpoint, so statement adequacy needs nothing from context adequacy. The two meet only
in downstream corollaries (e.g. the REC regression), never in this theorem.
-/

namespace RMFoundationBridge

open LO LO.FirstOrder LO.SecondOrder
open ReverseMathlib.Omega

/-- **The ŴKL sentence**: `∀²T ((Tree(T) ∧ Level(T)) → ∃²P Path(P, T))`, over the
canonical `seqCode` coding. -/
def wklSentence : SecondOrder.Sentence ℒₒᵣ :=
  .all₂ (impF (treeFormula 0 ⋏ levelFormula 0) (.exs₂ (pathFormula 0 1)))

/-- **The unconditional statement adapter**: for an arbitrary second-order part,
satisfaction of the ŴKL sentence is exactly the frozen `WeakKonigAt`. No `IsTuringIdeal`
premise — statement adequacy is independent of context adequacy. -/
theorem models_wklSentence_iff {Ω : OmegaPart} :
    Ω.toFoundation ⊧ wklSentence ↔ WeakKonigAt Ω := by
  have h : Ω.toFoundation ⊧ wklSentence ↔
      ∀ T : Set ℕ, T ∈ Ω.sets →
        EvalN Ω.sets
          (impF (treeFormula 0 ⋏ levelFormula 0) (.exs₂ (pathFormula 0 1)))
          (T :> ![]) ![] := Iff.rfl
  rw [h]
  constructor
  · intro hf T htree hlevel
    have hT := hf T.1 T.2
    rw [evalN_impF] at hT
    have hsplit : EvalN Ω.sets (treeFormula (0 : Fin 1) ⋏ levelFormula 0)
        (T.1 :> ![]) ![] ↔
        EvalN Ω.sets (treeFormula (0 : Fin 1)) (T.1 :> ![]) ![] ∧
        EvalN Ω.sets (levelFormula (0 : Fin 1)) (T.1 :> ![]) ![] := Iff.rfl
    have hconc := hT (hsplit.mpr
      ⟨(evalN_treeFormula 0 ![]).mpr htree, (evalN_levelFormula 0 ![]).mpr hlevel⟩)
    obtain ⟨P, hP, hpath⟩ := hconc
    exact ⟨⟨P, hP⟩,
      (evalN_pathFormula (𝕊 := Ω.sets) (E := ![P, T.1]) 0 1 ![]).mp hpath⟩
  · intro hwkl T hT
    rw [evalN_impF]
    intro hprem
    have hsplit : EvalN Ω.sets (treeFormula (0 : Fin 1) ⋏ levelFormula 0)
        (T :> ![]) ![] ↔
        EvalN Ω.sets (treeFormula (0 : Fin 1)) (T :> ![]) ![] ∧
        EvalN Ω.sets (levelFormula (0 : Fin 1)) (T :> ![]) ![] := Iff.rfl
    obtain ⟨htree, hlevel⟩ := hsplit.mp hprem
    obtain ⟨P, hpath⟩ := hwkl ⟨T, hT⟩ ((evalN_treeFormula 0 ![]).mp htree)
      ((evalN_levelFormula 0 ![]).mp hlevel)
    exact ⟨P.1, P.2,
      (evalN_pathFormula (𝕊 := Ω.sets) (E := ![P.1, T]) 0 1 ![]).mpr hpath⟩

end RMFoundationBridge

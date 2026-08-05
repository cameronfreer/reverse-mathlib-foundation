/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Omega.InverseSystem
import RMFoundationBridge.GraphPredicates

/-!
# F2, second layer: the EFILC sentence and the unconditional adapter

`efilcSentence` is exact explicit finite inverse-limit compactness as a closed `ℒₒᵣ`
second-order sentence, spelled field-by-field against the **frozen**
`InternalInverseSystem`: the two quantified sets are the fiber-enumerator graph and the
bonding graph (function-graph-ness quantified explicitly), the three side conditions
(nodup, nonempty, bonding-membership) are the frozen record fields verbatim, and the
conclusion asks for a section graph with the two frozen `IsSection` conditions.

**`models_efilcSentence_iff` is unconditional**: for an arbitrary second-order part `Ω`
— no Turing-ideal premise, no closure assumption — satisfaction is exactly the frozen
`EFILCAt Ω`. As with the ŴKL adapter, the second-order quantifiers already range over
`Ω.sets` and the coding agrees literally with the frozen endpoint, so no set
translation occurs anywhere. No derivation claims.
-/

namespace RMFoundationBridge

open LO LO.FirstOrder LO.SecondOrder
open ReverseMathlib.Omega

/-! ### Nested-pair membership -/

/-- `(n, x, y)`: the code `Nat.pair (Nat.pair n x) y` belongs to the set variable `X` —
membership of a curried-pair graph edge. -/
def pairMemPFormula {N : ℕ} (X : Fin N) :
    SecondOrder.Semiformula ℒₒᵣ Empty Empty N 3 :=
  .exs₁ (app₃ pairGraph #1 #2 #0 ⋏ app₂ (pairMemFormula X) #0 #3)

section pairMemP

variable {𝕊 : Set (Set ℕ)} {N n : ℕ} {E : Fin N → Set ℕ}

theorem evalN_pairMemPFormula (X : Fin N) (a x y : ℕ) :
    EvalN 𝕊 (pairMemPFormula X) E ![a, x, y] ↔
      Nat.pair (Nat.pair a x) y ∈ E X := by
  have h : EvalN 𝕊 (pairMemPFormula X) E ![a, x, y] ↔
      ∃ p : ℕ, EvalN 𝕊 (app₃ pairGraph #1 #2 #0) E (p :> ![a, x, y]) ∧
        EvalN 𝕊 (app₂ (pairMemFormula X) #0 #3) E (p :> ![a, x, y]) := Iff.rfl
  rw [h]
  constructor
  · rintro ⟨p, h₁, h₂⟩
    have h₁' : p = Nat.pair a x := (evalN_app₃_pairGraph _ _ _ _).mp h₁
    have h₂' : Nat.pair p y ∈ E X := (evalN_app₂_pairMemFormula X _ _ _).mp h₂
    rwa [h₁'] at h₂'
  · intro hmem
    exact ⟨Nat.pair a x, (evalN_app₃_pairGraph _ _ _ _).mpr rfl,
      (evalN_app₂_pairMemFormula X _ _ _).mpr hmem⟩

theorem evalN_app₃_pairMemPFormula (X : Fin N) (t₁ t₂ t₃ : Semiterm ℒₒᵣ Empty n)
    (e : Fin n → ℕ) :
    EvalN 𝕊 (app₃ (pairMemPFormula X) t₁ t₂ t₃) E e ↔
      Nat.pair (Nat.pair (tval t₁ e) (tval t₂ e)) (tval t₃ e) ∈ E X := by
  rw [evalN_app₃, evalN_pairMemPFormula]

end pairMemP

/-! ### The hypothesis and conclusion matrices -/

/-- The system hypothesis at set scope `(Gb, Gf) = (0, 1)`: both quantified sets are
function graphs; fibers decode nodup and nonempty; bonding maps fibers into fibers. -/
def efilcHypFormula : SecondOrder.Semiformula ℒₒᵣ Empty Empty 2 0 :=
  funGraphFormula 1 ⋏ funGraphFormula 0 ⋏
  .all₁ (.all₁ (impF (app₂ (pairMemFormula 1) #1 #0) (app₁ nodupFormula #0))) ⋏
  .all₁ (.all₁ (impF (app₂ (pairMemFormula 1) #1 #0) (app₁ nonNilFormula #0))) ⋏
  .all₁ (.all₁ (.all₁ (.all₁ (.all₁ (impF
    (app₂ (pairMemFormula 1) (tSucc #4) #3 ⋏ app₂ (pairMemFormula 1) #4 #2 ⋏
      app₂ memSeqFormula #3 #1 ⋏ app₃ (pairMemPFormula 0) #4 #1 #0)
    (app₂ memSeqFormula #2 #0))))))

/-- The section conclusion at set scope `(Gs, Gb, Gf) = (0, 1, 2)`: the witness set is a
function graph choosing fiber members coherently under the bonding maps. -/
def efilcConclFormula : SecondOrder.Semiformula ℒₒᵣ Empty Empty 3 0 :=
  funGraphFormula 0 ⋏
  .all₁ (.all₁ (.all₁ (impF
    (app₂ (pairMemFormula 2) #2 #1 ⋏ app₂ (pairMemFormula 0) #2 #0)
    (app₂ memSeqFormula #1 #0)))) ⋏
  .all₁ (.all₁ (.all₁ (impF
    (app₂ (pairMemFormula 0) (tSucc #2) #1 ⋏ app₂ (pairMemFormula 0) #2 #0)
    (app₃ (pairMemPFormula 1) #2 #1 #0))))

/-- **The EFILC sentence**: every explicit finite inverse system, presented by a fiber
enumerator graph and a bonding graph, has a section graph. -/
def efilcSentence : SecondOrder.Sentence ℒₒᵣ :=
  .all₂ (.all₂ (impF efilcHypFormula (.exs₂ efilcConclFormula)))

/-! ### Matrix adequacies -/

section matrices

variable {𝕊 : Set (Set ℕ)}

/-- Hypothesis adequacy, unbundled to the frozen record fields. -/
theorem evalN_efilcHypFormula (Gb Gf : Set ℕ) (e : Fin 0 → ℕ) :
    EvalN 𝕊 efilcHypFormula ![Gb, Gf] e ↔
      ((∀ x, ∃ y, Nat.pair x y ∈ Gf) ∧
        (∀ x y y', Nat.pair x y ∈ Gf ∧ Nat.pair x y' ∈ Gf → y = y')) ∧
      ((∀ x, ∃ y, Nat.pair x y ∈ Gb) ∧
        (∀ x y y', Nat.pair x y ∈ Gb ∧ Nat.pair x y' ∈ Gb → y = y')) ∧
      (∀ m c, Nat.pair m c ∈ Gf → (decodeSeq c).Nodup) ∧
      (∀ m c, Nat.pair m c ∈ Gf → decodeSeq c ≠ []) ∧
      (∀ m c c' x y, Nat.pair (m + 1) c ∈ Gf ∧ Nat.pair m c' ∈ Gf ∧
        x ∈ decodeSeq c ∧ Nat.pair (Nat.pair m x) y ∈ Gb → y ∈ decodeSeq c') := by
  have h : EvalN 𝕊 efilcHypFormula ![Gb, Gf] e ↔
      EvalN 𝕊 (funGraphFormula 1) ![Gb, Gf] e ∧
      EvalN 𝕊 (funGraphFormula 0) ![Gb, Gf] e ∧
      (∀ m c : ℕ, EvalN 𝕊 (impF (app₂ (pairMemFormula 1) #1 #0)
        (app₁ nodupFormula #0)) ![Gb, Gf] (c :> m :> e)) ∧
      (∀ m c : ℕ, EvalN 𝕊 (impF (app₂ (pairMemFormula 1) #1 #0)
        (app₁ nonNilFormula #0)) ![Gb, Gf] (c :> m :> e)) ∧
      (∀ m c c' x y : ℕ, EvalN 𝕊 (impF
        (app₂ (pairMemFormula 1) (tSucc #4) #3 ⋏ app₂ (pairMemFormula 1) #4 #2 ⋏
          app₂ memSeqFormula #3 #1 ⋏ app₃ (pairMemPFormula 0) #4 #1 #0)
        (app₂ memSeqFormula #2 #0)) ![Gb, Gf]
        (y :> x :> c' :> c :> m :> e)) := Iff.rfl
  rw [h]
  refine and_congr (evalN_funGraphFormula 1 e) (and_congr (evalN_funGraphFormula 0 e)
    (and_congr ?_ (and_congr ?_ ?_)))
  · refine forall_congr' fun m => forall_congr' fun c => ?_
    rw [evalN_impF]
    exact imp_congr (evalN_app₂_pairMemFormula 1 _ _ _) (evalN_app₁_nodupFormula _ _)
  · refine forall_congr' fun m => forall_congr' fun c => ?_
    rw [evalN_impF]
    exact imp_congr (evalN_app₂_pairMemFormula 1 _ _ _) (evalN_app₁_nonNilFormula _ _)
  · refine forall_congr' fun m => forall_congr' fun c => forall_congr' fun c' =>
      forall_congr' fun x => forall_congr' fun y => ?_
    rw [evalN_impF]
    have h2 : EvalN 𝕊
        (app₂ (pairMemFormula 1) (tSucc #4) #3 ⋏ app₂ (pairMemFormula 1) #4 #2 ⋏
          app₂ memSeqFormula #3 #1 ⋏ app₃ (pairMemPFormula 0) #4 #1 #0) ![Gb, Gf]
        (y :> x :> c' :> c :> m :> e) ↔
        EvalN 𝕊 (app₂ (pairMemFormula 1) (tSucc #4) #3) ![Gb, Gf]
          (y :> x :> c' :> c :> m :> e) ∧
        EvalN 𝕊 (app₂ (pairMemFormula 1) #4 #2) ![Gb, Gf]
          (y :> x :> c' :> c :> m :> e) ∧
        EvalN 𝕊 (app₂ memSeqFormula #3 #1) ![Gb, Gf]
          (y :> x :> c' :> c :> m :> e) ∧
        EvalN 𝕊 (app₃ (pairMemPFormula 0) #4 #1 #0) ![Gb, Gf]
          (y :> x :> c' :> c :> m :> e) := Iff.rfl
    rw [h2]
    exact imp_congr
      (and_congr (evalN_app₂_pairMemFormula 1 _ _ _)
        (and_congr (evalN_app₂_pairMemFormula 1 _ _ _)
          (and_congr (evalN_app₂_memSeqFormula _ _ _)
            (evalN_app₃_pairMemPFormula 0 _ _ _ _))))
      (evalN_app₂_memSeqFormula _ _ _)

/-- Conclusion adequacy, unbundled to the frozen `IsSection` conditions. -/
theorem evalN_efilcConclFormula (Gs Gb Gf : Set ℕ) (e : Fin 0 → ℕ) :
    EvalN 𝕊 efilcConclFormula ![Gs, Gb, Gf] e ↔
      ((∀ x, ∃ y, Nat.pair x y ∈ Gs) ∧
        (∀ x y y', Nat.pair x y ∈ Gs ∧ Nat.pair x y' ∈ Gs → y = y')) ∧
      (∀ m c v, Nat.pair m c ∈ Gf ∧ Nat.pair m v ∈ Gs → v ∈ decodeSeq c) ∧
      (∀ m v v', Nat.pair (m + 1) v ∈ Gs ∧ Nat.pair m v' ∈ Gs →
        Nat.pair (Nat.pair m v) v' ∈ Gb) := by
  have h : EvalN 𝕊 efilcConclFormula ![Gs, Gb, Gf] e ↔
      EvalN 𝕊 (funGraphFormula 0) ![Gs, Gb, Gf] e ∧
      (∀ m c v : ℕ, EvalN 𝕊 (impF
        (app₂ (pairMemFormula 2) #2 #1 ⋏ app₂ (pairMemFormula 0) #2 #0)
        (app₂ memSeqFormula #1 #0)) ![Gs, Gb, Gf] (v :> c :> m :> e)) ∧
      (∀ m v v' : ℕ, EvalN 𝕊 (impF
        (app₂ (pairMemFormula 0) (tSucc #2) #1 ⋏ app₂ (pairMemFormula 0) #2 #0)
        (app₃ (pairMemPFormula 1) #2 #1 #0)) ![Gs, Gb, Gf]
        (v' :> v :> m :> e)) := Iff.rfl
  rw [h]
  refine and_congr (evalN_funGraphFormula 0 e) (and_congr ?_ ?_)
  · refine forall_congr' fun m => forall_congr' fun c => forall_congr' fun v => ?_
    rw [evalN_impF]
    have h2 : EvalN 𝕊 (app₂ (pairMemFormula 2) #2 #1 ⋏
        app₂ (pairMemFormula 0) #2 #0) ![Gs, Gb, Gf] (v :> c :> m :> e) ↔
        EvalN 𝕊 (app₂ (pairMemFormula 2) #2 #1) ![Gs, Gb, Gf] (v :> c :> m :> e) ∧
        EvalN 𝕊 (app₂ (pairMemFormula 0) #2 #0) ![Gs, Gb, Gf] (v :> c :> m :> e) :=
      Iff.rfl
    rw [h2]
    exact imp_congr
      (and_congr (evalN_app₂_pairMemFormula 2 _ _ _)
        (evalN_app₂_pairMemFormula 0 _ _ _))
      (evalN_app₂_memSeqFormula _ _ _)
  · refine forall_congr' fun m => forall_congr' fun v => forall_congr' fun v' => ?_
    rw [evalN_impF]
    have h2 : EvalN 𝕊 (app₂ (pairMemFormula 0) (tSucc #2) #1 ⋏
        app₂ (pairMemFormula 0) #2 #0) ![Gs, Gb, Gf] (v' :> v :> m :> e) ↔
        EvalN 𝕊 (app₂ (pairMemFormula 0) (tSucc #2) #1) ![Gs, Gb, Gf]
          (v' :> v :> m :> e) ∧
        EvalN 𝕊 (app₂ (pairMemFormula 0) #2 #0) ![Gs, Gb, Gf]
          (v' :> v :> m :> e) := Iff.rfl
    rw [h2]
    exact imp_congr
      (and_congr (evalN_app₂_pairMemFormula 0 _ _ _)
        (evalN_app₂_pairMemFormula 0 _ _ _))
      (evalN_app₃_pairMemPFormula 1 _ _ _ _)

end matrices

/-! ### The unconditional adapter -/

/-- **The unconditional statement adapter for EFILC**: for an arbitrary second-order
part, satisfaction of the EFILC sentence is exactly the frozen `EFILCAt`. -/
theorem models_efilcSentence_iff {Ω : OmegaPart} :
    Ω.toFoundation ⊧ efilcSentence ↔ EFILCAt Ω := by
  have h : Ω.toFoundation ⊧ efilcSentence ↔
      ∀ Gf : Set ℕ, Gf ∈ Ω.sets → ∀ Gb : Set ℕ, Gb ∈ Ω.sets →
        EvalN Ω.sets (impF efilcHypFormula (.exs₂ efilcConclFormula))
          ![Gb, Gf] ![] := Iff.rfl
  rw [h]
  constructor
  · intro hf F
    have hF := hf F.fibers.graph.1 F.fibers.graph.2 F.bonding.graph.1 F.bonding.graph.2
    rw [evalN_impF] at hF
    have hhyp := (evalN_efilcHypFormula (𝕊 := Ω.sets)
        F.bonding.graph.1 F.fibers.graph.1 ![]).mpr
      ⟨⟨F.fibers.total, fun x y y' hp => F.fibers.singleValued x y y' hp.1 hp.2⟩,
       ⟨F.bonding.total, fun x y y' hp => F.bonding.singleValued x y y' hp.1 hp.2⟩,
       fun m c hc => F.fiber_nodup m c hc,
       fun m c hc => F.fiber_nonempty m c hc,
       fun m c c' x y hp => F.bonding_mem m c c' x y hp.1 hp.2.1 hp.2.2.1 hp.2.2.2⟩
    obtain ⟨Gs, hGs, hconcl⟩ := hF hhyp
    have hc := (evalN_efilcConclFormula (𝕊 := Ω.sets)
      Gs F.bonding.graph.1 F.fibers.graph.1 ![]).mp hconcl
    refine ⟨⟨⟨Gs, hGs⟩, hc.1.1, fun x y y' h1 h2 => hc.1.2 x y y' ⟨h1, h2⟩⟩, ?_, ?_⟩
    · exact fun m c v hcm hvm => hc.2.1 m c v ⟨hcm, hvm⟩
    · exact fun m v v' hv hv' => hc.2.2 m v v' ⟨hv, hv'⟩
  · intro hE Gf hGf Gb hGb
    rw [evalN_impF]
    intro hhyp
    have hh := (evalN_efilcHypFormula (𝕊 := Ω.sets) Gb Gf ![]).mp hhyp
    set F : InternalInverseSystem Ω :=
      { fibers := ⟨⟨Gf, hGf⟩, hh.1.1, fun x y y' h1 h2 => hh.1.2 x y y' ⟨h1, h2⟩⟩
        bonding := ⟨⟨Gb, hGb⟩, hh.2.1.1, fun x y y' h1 h2 => hh.2.1.2 x y y' ⟨h1, h2⟩⟩
        fiber_nodup := fun m c hc => hh.2.2.1 m c hc
        fiber_nonempty := fun m c hc => hh.2.2.2.1 m c hc
        bonding_mem := fun m c c' x y h1 h2 h3 h4 =>
          hh.2.2.2.2 m c c' x y ⟨h1, h2, h3, h4⟩ } with hFdef
    obtain ⟨s, hs⟩ := hE F
    refine ⟨s.graph.1, s.graph.2, ?_⟩
    refine (evalN_efilcConclFormula (𝕊 := Ω.sets) s.graph.1 Gb Gf ![]).mpr
      ⟨⟨s.total, fun x y y' hp => s.singleValued x y y' hp.1 hp.2⟩, ?_, ?_⟩
    · exact fun m c v hp => hs.1 m c v hp.1 hp.2
    · exact fun m v v' hp => hs.2 m v v' hp.1 hp.2

end RMFoundationBridge
